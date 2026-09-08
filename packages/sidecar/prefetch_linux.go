//go:build linux

package main

import (
	"os"
	"syscall"

	"golang.org/x/sys/unix"
)

func mkfifo(path string) error {
	return syscall.Mkfifo(path, 0600)
}

// growPipeBuffer raises the named pipe's kernel buffer past the 64KB
// default; see the doc comment on prefetchPipeSize in main.go for why.
func growPipeBuffer(f *os.File, size int) {
	raw, err := f.SyscallConn()
	if err != nil {
		return
	}
	raw.Control(func(fd uintptr) {
		if _, err := unix.FcntlInt(fd, unix.F_SETPIPE_SZ, size); err != nil {
			debugf("[Prefetch] Could not grow pipe buffer, continuing with default size: %v", err)
		}
	})
}
