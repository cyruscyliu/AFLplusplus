/*
   american fuzzy lop++ - afl++-net based on afl-proxy
   ---------------------------------------------------

   Written by Marc Heuse <mh@mh-sec.de>
   Written by Qiang Liu <cyruscyliu@gmail.com>

   Copyright 2019-2024 AFLplusplus Project. All rights reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at:

   Usage
   - compile aflpp
   - compile the network server with afl-cc or afl-fast-clang
   - make sure the configuration of network server is correct
   - fuzz the network server
   - use AFL_DEBUG=1 for more logs

  ```
  /path/to/AFLplusplus/afl-fuzz -i ../in-ftp/ -o ../outputs -- \
    /path/to/AFLplusplus/utils/aflpp_net/aflpp-net -N tcp://127.0.0.1/2100 -- \
    ./bftpd -D -c ../basic.conf
  ```

   http://www.apache.org/licenses/LICENSE-2.0
*/

#ifdef __ANDROID__
  #include "android-ashmem.h"
#endif
#include "config.h"
#include "types.h"
#include "debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include <unistd.h>
#include <string.h>
#include <assert.h>
#include <stdint.h>
#include <errno.h>
#include <poll.h>

#include <sys/mman.h>
#include <sys/shm.h>
#include <sys/wait.h>
#include <sys/types.h>
#include <fcntl.h>
#include <arpa/inet.h>
#include <sys/time.h>

u8 *__afl_area_ptr;

#ifdef __ANDROID__
u32 __afl_map_size = MAP_SIZE;
#else
__thread u32 __afl_map_size = MAP_SIZE;
#endif

/* Error reporting to forkserver controller */

void send_forkserver_error(int error) {
  u32 status;
  if (!error || error > 0xffff) return;
  status = (FS_OPT_ERROR | FS_OPT_SET_ERROR(error));
  if (write(FORKSRV_FD + 1, (char *)&status, 4) != 4) return;
}

/* SHM setup. */

static void __afl_map_shm(void) {
  char *id_str = getenv(SHM_ENV_VAR);
  char *ptr;

  /* NOTE TODO BUG FIXME: if you want to supply a variable sized map then
     uncomment the following: */

  /*
  if ((ptr = getenv("AFL_MAP_SIZE")) != NULL) {

    u32 val = atoi(ptr);
    if (val > 0) __afl_map_size = val;

  }
  */

  if (__afl_map_size > MAP_SIZE) {
    if (__afl_map_size > FS_OPT_MAX_MAPSIZE) {
      fprintf(stderr,
              "Error: AFL++ tools *require* to set AFL_MAP_SIZE to %u to "
              "be able to run this instrumented program!\n",
              __afl_map_size);
      if (id_str) {
        send_forkserver_error(FS_ERROR_MAP_SIZE);
        exit(-1);
      }

    } else {
      fprintf(stderr,
              "Warning: AFL++ tools will need to set AFL_MAP_SIZE to %u to "
              "be able to run this instrumented program!\n",
              __afl_map_size);
    }
  }

  if (id_str) {
#ifdef USEMMAP
    const char    *shm_file_path = id_str;
    int            shm_fd = -1;
    unsigned char *shm_base = NULL;

    /* create the shared memory segment as if it was a file */
    shm_fd = shm_open(shm_file_path, O_RDWR, 0600);
    if (shm_fd == -1) {
      fprintf(stderr, "shm_open() failed\n");
      send_forkserver_error(FS_ERROR_SHM_OPEN);
      exit(1);
    }

    /* map the shared memory segment to the address space of the process */
    shm_base =
        mmap(0, __afl_map_size, PROT_READ | PROT_WRITE, MAP_SHARED, shm_fd, 0);

    if (shm_base == MAP_FAILED) {
      close(shm_fd);
      shm_fd = -1;

      fprintf(stderr, "mmap() failed\n");
      send_forkserver_error(FS_ERROR_MMAP);
      exit(2);
    }

    __afl_area_ptr = shm_base;
#else
    u32 shm_id = atoi(id_str);

    __afl_area_ptr = shmat(shm_id, 0, 0);

#endif

    if (__afl_area_ptr == (void *)-1) {
      send_forkserver_error(FS_ERROR_SHMAT);
      exit(1);
    }

    /* Write something into the bitmap so that the parent doesn't give up */

    __afl_area_ptr[0] = 1;
  }
}

/* Fork server logic. */

static void __afl_start_forkserver(void) {
  u8  tmp[4] = {0, 0, 0, 0};
  u32 status = 0;

  if (__afl_map_size <= FS_OPT_MAX_MAPSIZE)
    status |= (FS_OPT_SET_MAPSIZE(__afl_map_size) | FS_OPT_MAPSIZE);
  if (status) status |= (FS_OPT_ENABLED);
  memcpy(tmp, &status, 4);

  /* Phone home and tell the parent that we're OK. */

  if (write(FORKSRV_FD + 1, tmp, 4) != 4) return;
}

static u32 __afl_next_testcase(u8 *buf, u32 max_len) {
  s32 status, res = 0xffffff;

  /* Wait for parent by reading from the pipe. Abort if read fails. */
  if (read(FORKSRV_FD, &status, 4) != 4) return 0;

  /* we have a testcase - read it */
  status = read(0, buf, max_len);

  /* report that we are starting the target */
  if (write(FORKSRV_FD + 1, &res, 4) != 4) return 0;

  return status;
}

static void __afl_end_testcase(void) {
  int status = 0xffffff;

  if (write(FORKSRV_FD + 1, &status, 4) != 4) exit(1);
}

/* This is were the testcase data is written into */
u8  request_buf[1024];
s32 request_buf_size;

enum {
  /* 00 */ PRO_TCP,
  /* 01 */ PRO_UDP
};

/* network-specific varaibles */
pid_t child_pid = 0;
u32   server_wait_usecs = 10000;
u32   poll_wait_msecs = 1;
u32   socket_timeout_usecs = 10000;
u32   server_process_usecs = 10000;
u8    net_protocol;
u8   *net_ip;
u32   net_port;

/* script to clean up the environment of the SUT -- make fuzzing more
 * deterministic */
u8 *cleanup_script;

u8 use_net = 0;
u8 server_wait = 0;
u8 server_process = 0;
u8 poll_wait = 0;
u8 socket_timeout = 0;
u8 terminate_child = 1;  // otherwise the server goes to TIME_WAIT

int str_split(char *a_str, const char *a_delim, char **result, int a_count) {
  char *token;
  int   count = 0;
  /* count number of tokens */
  /* get the first token */
  char *tmp1 = strdup(a_str);
  token = strtok(tmp1, a_delim);
  /* walk through other tokens */
  while (token != NULL) {
    count++;
    token = strtok(NULL, a_delim);
  }
  if (count != a_count) { return 1; }
  /* split input string, store tokens into result */
  count = 0;
  /* get the first token */
  token = strtok(a_str, a_delim);
  /* walk through other tokens */
  while (token != NULL) {
    result[count] = token;
    count++;
    token = strtok(NULL, a_delim);
  }
  free(tmp1);
  return 0;
}

void str_rtrim(char *a_str) {
  char *ptr = a_str;
  int   count = 0;
  while ((*ptr != '\n') && (*ptr != '\t') && (*ptr != ' ') &&
         (count < strlen(a_str))) {
    ptr++;
    count++;
  }
  if (count < strlen(a_str)) { *ptr = '\0'; }
}

int parse_net_config(u8 *net_config, u8 *protocol, u8 **ip, u32 *port) {
  char   buf[80];
  char **tokens;
  int    tokenCount = 3;

  tokens = (char **)malloc(sizeof(char *) * (tokenCount));

  if (strlen(net_config) > 80) { return 1; }

  strncpy(buf, net_config, strlen(net_config));
  str_rtrim(buf);

  if (!str_split(buf, "/", tokens, tokenCount)) {
    if (!strcmp(tokens[0], "tcp:")) {
      *protocol = PRO_TCP;
    } else if (!strcmp(tokens[0], "udp:")) {
      *protocol = PRO_UDP;
    } else {
      return 1;
    }

    // TODO: check the format of this IP address
    *ip = strdup(tokens[1]);

    *port = atoi(tokens[2]);
    if (*port == 0) { return 1; }
  } else {
    return 1;
  }
  free(tokens);
  return 0;
}

int net_send(int sockfd, struct timeval timeout, char *mem, unsigned int len) {
  unsigned int  byte_count = 0;
  int           n;
  struct pollfd pfd[1];
  pfd[0].fd = sockfd;
  pfd[0].events = POLLOUT;
  int rv = poll(pfd, 1, 1);
  setsockopt(sockfd, SOL_SOCKET, SO_SNDTIMEO, (char *)&timeout,
             sizeof(timeout));
  if (rv > 0) {
    if (pfd[0].revents & POLLOUT) {
      while (byte_count < len) {
        usleep(10);
        n = send(sockfd, &mem[byte_count], len - byte_count, MSG_NOSIGNAL);
        if (n == 0) return byte_count;
        if (n == -1) return -1;
        byte_count += n;
      }
    }
  }
  return byte_count;
}

int net_recv(int sockfd, struct timeval timeout, int poll_w,
             char **response_buf, unsigned int *len) {
  char          temp_buf[1000];
  int           n;
  struct pollfd pfd[1];
  pfd[0].fd = sockfd;
  pfd[0].events = POLLIN;
  int rv = poll(pfd, 1, poll_w);
  setsockopt(sockfd, SOL_SOCKET, SO_RCVTIMEO, (char *)&timeout,
             sizeof(timeout));
  if (rv > 0) {
    if (pfd[0].revents & POLLIN) {
      n = recv(sockfd, temp_buf, sizeof(temp_buf), 0);
      if ((n < 0) && (errno != 11)) {
        fprintf(stderr, "\nError no is: %d\n", errno);
        return 1;
      }
      while (n > 0) {
        usleep(10);
        *response_buf = (unsigned char *)realloc(*response_buf, *len + n);
        memcpy(&(*response_buf)[*len], temp_buf, n);
        *len = *len + n;
        n = recv(sockfd, temp_buf, sizeof(temp_buf), 0);
        if ((n < 0) && (errno != 11)) {
          fprintf(stderr, "\nError no is: %d\n", errno);
          return 1;
        }
      }
    }
  } else if (rv < 0) {
    return 1;
  }
  return 0;
}

int send_over_network() {
  int                n;
  struct sockaddr_in serv_addr;

  // clean up the server if needed
  if (cleanup_script) system(cleanup_script);

  // create a TCP/UDP socket
  int sockfd = -1;
  if (net_protocol == PRO_TCP) {
    sockfd = socket(AF_INET, SOCK_STREAM, 0);
  } else if (net_protocol == PRO_UDP) {
    sockfd = socket(AF_INET, SOCK_DGRAM, 0);
  }
  if (sockfd < 0) { PFATAL("Cannot create a socket"); }

  // set timeout for socket data sending/receiving -- otherwise it causes a big
  // delay if the server is still alive after processing all the requests
  struct timeval timeout;
  timeout.tv_sec = 0;
  timeout.tv_usec = socket_timeout_usecs;
  setsockopt(sockfd, SOL_SOCKET, SO_SNDTIMEO, (char *)&timeout,
             sizeof(timeout));

  memset(&serv_addr, '0', sizeof(serv_addr));
  serv_addr.sin_family = AF_INET;
  serv_addr.sin_port = htons(net_port);
  serv_addr.sin_addr.s_addr = inet_addr(net_ip);

  if (connect(sockfd, (struct sockaddr *)&serv_addr, sizeof(serv_addr)) < 0) {
    DEBUGF("Socket not properly closed on the server side (TIME_WAIT)\n");
    // If it cannot connect to the server under test
    // try it again as the server initial startup time is varied
    for (n = 0; n < 1000; n++) {
      if (connect(sockfd, (struct sockaddr *)&serv_addr, sizeof(serv_addr)) ==
          0) {
        break;
      }
      usleep(1000);
    }
    if (n == 1000) {
      close(sockfd);
      return 1;
    }
  }

  char *response_buf = NULL;
  int   response_buf_size = 0;

  // retrieve early server response if needed
  if (net_recv(sockfd, timeout, poll_wait_msecs, &response_buf,
               &response_buf_size)) {
    goto HANDLE_RESPONSES;
  }

  // write the requests stored in the generated seed input
  n = net_send(sockfd, timeout, request_buf, request_buf_size);

HANDLE_RESPONSES:
  net_recv(sockfd, timeout, poll_wait_msecs, &response_buf, &response_buf_size);

  // wait a bit letting the server to complete its remaing task(s)
  usleep(server_process_usecs);
  close(sockfd);

  if (response_buf) { free(response_buf); }
  return 0;
}

int main(int argc, char *argv[]) {
  /* here you specify the map size you need that you are reporting to
     afl-fuzz.  Any value is fine as long as it can be divided by 32. */
  __afl_map_size = MAP_SIZE;  // default is 65536

  /* then we initialize the shared memory map and start the forkserver */
  __afl_map_shm();
  __afl_start_forkserver();

  DEBUGF("Hello! We are in aflpp-net!\n");

  int opt;
  while ((opt = getopt(argc, argv, "N:D:d:W:w:c:")) > 0) {
    switch (opt) {
      case 'N': /* network configuration */
        if (use_net) { FATAL("Multiple -N options not supported"); }
        if (parse_net_config(optarg, &net_protocol, &net_ip, &net_port)) {
          FATAL(
              "Bad syntax used for -N. Check the network setting. "
              "[tcp/udp]://127.0.0.1/port");
        }
        use_net = 1;
        break;
      case 'D': /* waiting time for the server initialization */
        if (server_wait) { FATAL("Multiple -D options not supported"); }
        if (sscanf(optarg, "%u", &server_wait_usecs) < 1 || optarg[0] == '-') {
          FATAL("Bad syntax used for -D");
        }
        server_wait = 1;
        break;
      case 'd': /* waiting time for the server processing*/
        if (server_process) { FATAL("Multiple -d options not supported"); }
        if (sscanf(optarg, "%u", &server_process_usecs) < 1 ||
            optarg[0] == '-') {
          FATAL("Bad syntax used for -d");
        }
        server_process = 1;
        break;
      case 'W': /* polling timeout determining maximum amount of time waited
                   before concluding that no responses are forthcoming*/
        if (poll_wait) { FATAL("Multiple -W options not supported"); }
        if (sscanf(optarg, "%u", &poll_wait_msecs) < 1 || optarg[0] == '-') {
          FATAL("Bad syntax used for -W");
        }
        poll_wait = 1;
        break;
      case 'w': /* receive/send socket timeout determining time waited for each
                   response */
        if (socket_timeout) { FATAL("Multiple -w options not supported"); }
        if (sscanf(optarg, "%u", &socket_timeout_usecs) < 1 ||
            optarg[0] == '-') {
          FATAL("Bad syntax used for -w");
        }
        socket_timeout = 1;
        break;
      case 'c': /* cleanup script */
        if (cleanup_script) FATAL("Multiple -c options not supported");
        cleanup_script = optarg;
        break;
    }
  }

  DEBUGF("Nice! We've parsed aflpp-net's arguments!\n");

  // remaining arguments after --
  if (optind >= argc || strcmp(argv[optind - 1], "--") != 0) {
    FATAL("Error: Missing -- followed by command to execute.\n");
  }

  // skip the "--" marker
  if (optind >= argc) { FATAL("Error: No command specified to execute.\n"); }

  // prepare to launch the network server
  char **command = &argv[optind];

  DEBUGF("Nice! We've got network server's arguments!\n");

  while ((request_buf_size =
              __afl_next_testcase(request_buf, sizeof(request_buf))) > 0) {
    DEBUGF("Wow! We've got a testcase from aflpp!\n");

    if (child_pid == 0) {
      child_pid = fork();
      if (child_pid < 0) { FATAL("fork"); }
      if (child_pid == 0) {
        close(FORKSRV_FD);
        close(FORKSRV_FD + 1);
        execvp(command[0], command);
        FATAL("execvp");  // execvp only returns on error
      } else {
        usleep(server_wait_usecs);
      }
    }
    int status;

    DEBUGF("Allez! Allez!\n");
    send_over_network();
    DEBUGF("Bingo! We've sent the testcase to the network server!\n");

    if (terminate_child) {
      kill(child_pid, SIGTERM);
      waitpid(child_pid, &status, 0);
      child_pid = 0;

      if (WIFEXITED(status)) {
        DEBUGF("Child exited with status %d\n", WEXITSTATUS(status));
      } else if (WIFSIGNALED(status)) {
        DEBUGF("Child terminated by signal %d\n", WTERMSIG(status));
      }
    }
    /* report the test case is done and wait for the next */
    __afl_end_testcase();
  }
  return 0;
}
