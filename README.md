# TRADINGBOTPROJECT
Kalshi NBA Trading Bot
A Python system that trades Kalshi's NBA prediction markets. It combines live ESPN and Kalshi score feeds to find spread and total markets that are already mathematically decided late in a quarter, then buys the winning side at 95–99¢.

Features: WebSocket price streaming, rate-limited concurrent order routing, cross-checking of independent data sources, overtime and score-correction safeguards, position and daily-loss limits, and full trade/signal logging.

Testing: The strategy was validated by paper trading and by reviewing every loss to find and fix its cause. Over 5 days (791 simulated trades), the paper results were a 99.9% win rate and a 1.7% return on capital risked. Simulated fills are optimistic: live trading fills far less often because other traders reach the same prices first, so these are not real-money returns.

Lessons: Early versions lost money on score-feed errors and overtime edge cases. Each loss led to a new safeguard.
