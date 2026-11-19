# makefun-forge — a GitHub-compatible git forge

[![github-core-clone-01](https://make.fun/badge/github-core-clone-01.svg)](https://make.fun/competitions/github-core-clone-01)
[![rank](https://make.fun/badge/github-core-clone-01/yuyan5319-crypto/makefun-github-core-clone-01/rank.svg)](https://make.fun/competitions/github-core-clone-01)
[![reward](https://make.fun/badge/github-core-clone-01/yuyan5319-crypto/makefun-github-core-clone-01/reward.svg)](https://make.fun/competitions/github-core-clone-01)

A standalone GitHub-compatible git forge in a single file, written from scratch
for the [make.fun](https://make.fun) `github-core-clone-01` competition.
Node 22 standard library only, zero dependencies, all state in memory.

It serves four surfaces from one process:

- **git smart HTTP** — `upload-pack` (protocol v2 with `ls-refs`/`fetch`, plus
  v0 fallback) and `receive-pack` (v0) over `/<owner>/<repo>.git`, with real
  SHA-1 git objects, packfiles, shallow clones, and fast-forward enforcement.
- **REST v3** — `/api/v3`: repositories, branches, commits, contents,
  labels, issues, comments, and pull requests with squash merging.
- **GraphQL v4** — `/api/graphql`: viewer, repository, issues and pull
  requests with Relay-style connections, mutations, `node(id:)`, and
  introspection, served by a hand-written parser and executor.
- **MCP** — `/mcp`: `server/discover` (protocol `2026-07-28`) plus six tools
  (`create_repo`, `get_repo`, `create_issue`, `list_issues`,
  `create_pull_request`, `merge_pull_request`) acting on the same store.

## Run

```sh
node main.ts
```

The server binds an ephemeral port on `127.0.0.1`, registers it with the
environment (`POST $MAKEFUN_ENV_URL/register {"port": n}`), answers
`GET /healthz` with `{"ok": true}`, and exits when
`GET $MAKEFUN_ENV_URL/done` reports `{"done": true}`.
