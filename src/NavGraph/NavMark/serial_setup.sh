#!/bin/bash
user=piac6784
rm /dev/ttyS0 
killall -9 socat
socat pty,link=/dev/ttyS0,raw,echo=0 pty,link=/tmp/serial,raw,echo=0 &
sleep 2
chown ${user} /dev/ttyS0
chown ${user} /tmp/serial


