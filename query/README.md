# xash3d-query

Receive and display information about servers.

# Usage

Fetch information about a server.

```sh
$ xash3d-query info 144.49.47.88:27016
server: 144.49.47.88:27016 [33.462 ms]
    status: "ok"
    host: "Test Server"
    gamedir: "valve"
    map: "crossfire"
    protocol: "0"
    numcl: "13"
    maxcl: "30"
    dm: "true"
    team: "false"
    coop: "false"
    password: "false"
```

Fetch servers addresses from the master server.

```sh
$ xash3d-query list
144.49.47.88:27016
144.49.47.88:27017
```

Fetch information about all servers received from the master server.

```sh
$ xash3d-query
server: 144.49.47.88:27016 [33.462 ms]
    status: "ok"
    host: "Test Server"
    gamedir: "valve"
    map: "crossfire"
    protocol: "0"
    numcl: "13"
    maxcl: "30"
    dm: "true"
    team: "false"
    coop: "false"
    password: "false"

server: 144.49.47.88:27017 [32.596 ms]
    status: "ok"
    host: "Test Server 2"
    gamedir: "valve"
    map: "crossfire"
    protocol: "0"
    numcl: "7"
    maxcl: "30"
    dm: "true"
    team: "false"
    coop: "false"
    password: "false"
```

# JSON output

```sh
# Print table sorted by number of players.
$ xash3d-query -j | jq -r '[.servers[] | select(.status == "ok")] | sort_by(.numcl) | reverse | .[] | [.numcl, .map, .address, .host] | @tsv'
13      crossfile       144.49.47.88:27016    Test Server
7       crossfile       144.49.47.88:27017    Test Server 2
```
