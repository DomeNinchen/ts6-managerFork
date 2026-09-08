//go:build !linux

package main

import (
	"fmt"
	"os"
)

// Named pipes are a Linux/Unix concept; on other platforms the prefetch
// buffer is simply unavailable and StartFFmpeg falls back to having ffmpeg
// read the network directly (see startPrefetch's caller in main.go). This
// only affects local non-Linux dev builds -- production always runs the
// Linux container image.
func mkfifo(path string) error {
	return fmt.Errorf("named pipes not supported on this platform")
}

func growPipeBuffer(f *os.File, size int) {}
