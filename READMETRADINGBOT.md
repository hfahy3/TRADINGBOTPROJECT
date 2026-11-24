# Kalshi NBA Decided-Market Trading Bot

A Python system that trades Kalshi's NBA prediction markets (quarter, half and whole-game point totals and spreads).
Late in a period some contracts are already decided, for example an "Over 54.5" whose line has been passed, or a
spread that cannot be overturned in the seconds that remain. The near-certain side often still trades at 95-99 cents.
The bot finds those moments from live game data, checks them against a set of safeguards, and buys the winning side.

> Paper trading is the default. Real orders require `--live`, a typed confirmation, and API keys provided through
> environment variables. Nothing here is investment advice.

## What it demonstrates
- **Real-time data engineering:** merges ESPN and Kalshi live score feeds, detects stale or contradictory data, and
  cross-checks the two sources.
- **Concurrency and systems work:** multi-threaded fast lane, token-bucket rate limiting per request type, per-thread
  HTTP sessions, a hand-written WebSocket client (stdlib only) with automatic reconnect and REST fallback.
- **Risk controls:** price band, overtime and score-correction rules, ladder check against neighbouring lines,
  per-game and per-event limits, exposure cap, daily loss stop, emergency stop file.
- **Measurement:** ledgers for every simulated and executed trade, a log of every signal (taken or skipped), and
  reports used to find and fix the cause of each loss.

## How it works
1. **Data:** ESPN scoreboard + Kalshi live feed and market data.
2. **Signal:** from score, clock and period, compute the most points that could still be scored (with a cushion for
   late put-backs and overturned baskets). If a contract cannot change outcome, it is a signal.
3. **Safeguards:** entry price band, source cross-checks, strict team-name matching, overtime rules for whole-game
   and 2nd-half markets, no late Unders in close games, position limits.
4. **Execution:** immediate-or-cancel buys that take only what is already for sale, sized as a percentage of the account.
5. **Logging:** every signal and trade is recorded for review.

## Results (paper trading, honest version)
| Period | Simulated trades | Losses | Return on dollars risked |
|---|---|---|---|
| Nov 10-17 (early version) | 1,438 | 18 | 0.6% |
| Nov 18-22 (after safeguards) | 791 | 1 | 1.7% |

Paper results are optimistic. They assume a fill at the quoted price, but live fills are limited by how much is for
sale and by faster competing traders, so these are **not real-money returns**. The break-even miss rate is roughly
2 losses per 100 trades, so a few losses can erase many wins; that risk drives most of the safeguards.

## Lessons learned
Early versions lost money to score-feed errors, quarter-split mismatches between data sources, and overtime edge
cases. Each loss led to a new safeguard: observed period ends, a ladder check, overtime blocks, final-score
cushions and stricter team matching.

## Run it
```bash
pip install requests cryptography
python3 kalshi_nba_bot.py --check      # today's games and matching markets
python3 kalshi_nba_bot.py              # paper trading
python3 kalshi_nba_bot.py --report     # summary of paper trades
```
Live trading (real money) needs `KALSHI_API_KEY_ID` and `KALSHI_PRIVATE_KEY_PATH` in your environment and
`--live`. Keep keys out of the repository.
