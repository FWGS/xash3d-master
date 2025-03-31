## Simple installation guide
### Prerequisites:
For now, `xash3d-master` is only built for GNU/Linux x86_64, ARM64 and RISC-V systems. If you have something different, try compiling it from source code. `xash3d-master` is super lightweight and even with current server load requires less than a megabyte of memory and single core CPU. During installation process, you would need to have `wget`, `zstd` and `tar` utilities installed. We also only support `systemd` as system daemon manager.
### Installation:
In your server console from root user, execute:
```
# wget https://github.com/FWGS/xash3d-master/releases/download/continuous/xash3d-master-`uname -m`-unknown-linux-gnu.tar.zst -qO- | tar --zstd -xvf -
```
Now move unpacked files into it's appropriate places: binaries into `/usr/local/bin` and config file to `/etc/xash3d-master/`
```
# mkdir -p /usr/local/bin /etc/xash3d-master
# mv xash3d-admin xash3d-query xash3d-master /usr/local/bin
# mv config.toml /etc/xash3d-master
```
Configure master-server for IPv4 and IPv6 address. In this guide we will call separate config files for IPv4 as `v4` and IPv6 as `v6`. If you don't have either IPv4 or IPv6, you can skip configuring them.
```
# cd /etc/xash3d-master
# cp config.toml v4.toml
# cp config.toml v6.toml
```
Now with your editor of choice, edit `v4.toml` and `v6.toml`. Note that there is at least one option that you have set up properly, which is `ip` in `[server]`. Finally, you need to install `systemd` unit and enable it:
```
# wget https://raw.githubusercontent.com/FWGS/xash3d-master/refs/heads/master/xash3d-master%40.service -O /etc/systemd/system/xash3d-master\@.service
# systemctl daemon-reload
# systemctl enable --now xash3d-master@v4 xash3d-master@v6
```
Validate that server is running with `systemctl status xash3d-master@v4 xash3d-master@v6` command. You can also test with `xash3d-query` utility or just add your master server IP address to `xashcomm.lst` file in the game directory in following format:
```
master <IPv4 address>:27010
master <IPv6 address>:27010
```
### Contributing it to Xash3D FWGS
If you're willing to make your master server public for everyone, properly [moderate it](https://github.com/FWGS/xash3d-fwgs/blob/master/Documentation/public-servers-rules-and-recommendations.md), you can contribute it to Xash3D FWGS. For that open a pull request adding your master server address in `NET_MastersInit` function in the `engine/common/masterlist.c` [file](https://github.com/FWGS/xash3d-fwgs/blob/master/engine/common/masterlist.c).
