[![make.fun](https://make.fun/competitions/github-core-clone-01)](https://make.fun/competitions/github-core-clone-01)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Node.js 22](https://img.shields.io/badge/Node.js-22-green.svg)](https://nodejs.org/)

# github-core-clone-01

A standalone, GitHub-compatible git forge in a single Node.js process
(standard library only, zero dependencies).

It serves git smart HTTP (upload-pack protocol v2, receive-pack v0),
the REST v3 API under `/api/v3`, the GraphQL v4 API at `/api/graphql`,
and a Model Context Protocol endpoint at `/mcp` — all from its own
in-memory store, with no outside service, no proxy and no git binary.

## Run

```sh
node main.ts
```

The process binds an ephemeral port, registers it with
`$MAKEFUN_ENV_URL/register`, answers `GET /healthz`, and long-polls
`$MAKEFUN_ENV_URL/done` until the suite finishes, then exits 0.

## Layout

- `main.ts` — the whole forge: HTTP server, git packfile/protocol
  implementation, REST v3, GraphQL v4 and MCP.
- `LICENSE` — MIT.
