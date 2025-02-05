#Readme made from Chat so dont quote me

## Strategic Overview

The bot's gameplay is governed by a combination of preflop hand selection, postflop hand evaluation, opponent modeling, and auction bidding strategies.  These components are described in detail below.

### Preflop Hand Selection

The bot utilizes a preflop hand chart (`self.preflop_dict`) to guide its actions before the flop.  Hands are categorized and ranked, enabling the bot to raise aggressively with premium hands, call with mid-strength hands (contingent on the opponent's bet sizing), and fold weaker hands.  The bot's preflop aggression is modulated based on its position (big blind or not).

### Opponent Modeling

A rudimentary opponent model is maintained, tracking key opponent tendencies.  This model considers the opponent's aggression rate (betting frequency), pot bet ratio (bets as a proportion of the pot), and bluffing frequency (checks followed by bets). This information informs the bot's calling and raising decisions.  For instance, against an aggressive opponent, the bot will be more inclined to fold marginal hands and less prone to bluff.

### Hand Strength Evaluation

Hand strength is evaluated using a combination of methods:

*   **Preflop:**  Hand strength is estimated based on the preflop hand chart ranking.
*   **Postflop:** Monte Carlo simulation with the `eval7` library is employed to estimate hand equity against a range of potential opponent hands. The bot leverages `eval7.py_hand_vs_range_monte_carlo` for optimized performance where applicable, reverting to a manual simulation when necessary or preflop.  The simulation considers community cards and the bot's hole cards. The number of simulation trials is dynamically adjusted based on the remaining game clock and round number, decreasing as time becomes limited.

### Auction Bidding

During auction rounds (post-flop, turn, and river), the bot bids based on its hand strength and the current pot size.  A dedicated function (`self.auction_strength`) assesses the probability of winning the auction and the hand's strength with and without the auction card. The bid amount is calculated to maximize expected value, incorporating a degree of randomness. The `self.auction_factor` and `self.add_auction` parameters fine-tune the bidding strategy and are dynamically updated based on observed opponent behavior.

### Postflop Play

Postflop strategy encompasses checking, calling, raising, and folding, guided by hand strength, opponent actions, and pot odds.  Key elements include:

*   **Bluffing:** The bot incorporates bluffing into its strategic repertoire. Bluffing frequency is adjusted based on perceived opponent tendencies (e.g., check-raise frequency).  Distinct bluffing strategies are employed (two checks then raise, one check then raise, and general bluffs), with usage and success rates tracked and dynamically adjusted. The bot is less likely to bluff when it has already demonstrated aggression in the hand. The `self.try_bluff`, `self.bluff_fact`, `self.onebluff_fact`, and `self.twobluff_fact` parameters govern the various bluffing strategies.
*   **Value Betting:** Strong hands prompt value bets, aiming to extract chips from weaker hands.  Bet sizing is influenced by pot size and hand strength.
*   **Calling:** The bot calls with mid-strength hands when pot odds are favorable.  Calling frequency is reduced against aggressive opponents who make substantial pot-sized bets.
*   **Folding:** Weak hands or unfavorable pot odds lead to folding.

### Nit Strategy

A "nit" strategy (highly conservative play) is adopted when a significant chip lead is established, aiming to secure victory by minimizing risk.

### Dynamic Adjustments

Several parameters are dynamically adjusted during gameplay:

*   **Number of Trials:** The number of Monte Carlo simulation trials is reduced as the game clock decreases.
*   **Bluffing Frequency:**  The frequency of different bluffing strategies is adapted based on observed success rates.
*   **Auction Bidding:** The bidding strategy is adjusted in response to opponent bidding patterns.

## Execution

The bot requires the `skeleton` library (provided within the competition environment) and the `eval7` library.  Execution is performed by running the `player.py` script.

```bash
python player.py