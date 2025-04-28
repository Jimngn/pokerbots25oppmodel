# Goggins - Poker Bot Strategy and Implementation

Yes the readme is made by chat obviously 

## 1. Introduction

Goggins is designed to be a competitive poker bot that leverages preflop hand rankings, opponent modeling, auction bidding strategies, and postflop hand strength evaluation. The core principles guiding the bot's strategy are:

*   **Aggressive Preflop Play:** Seeking to gain an early advantage by selectively raising with strong starting hands.
*   **Data-Driven Auction Bidding:** Using Monte Carlo simulations to assess hand strength and bid strategically in the auction phase.
*   **Adaptive Postflop Decision-Making:** Adjusting actions based on hand strength, opponent tendencies, and pot odds.
*   **Opponent Modeling:** Tracking opponent behavior to exploit predictable patterns.

## 2. Core Components

The bot's implementation can be found in the `Player` class, derived from the `Bot` class provided in the `skeleton` framework. Key dependencies and libraries used include:

*   `skeleton`: A framework provided by the competition organizers, which defines the game states, actions, and rules.
*   `eval7`: A library for evaluating hand strength using Monte Carlo simulations.
*   `random`: A module used for introducing randomness into decision-making to avoid predictability.

## 3. Preflop Strategy: Comprehensive Analysis

The preflop strategy is the foundation of Goggins's overall game plan. It relies on a hand ranking dictionary (`self.preflop_dict`) and a set of rules that determine when to raise, call, or fold.

### 3.1. Hand Ranking Dictionary

The `self.preflop_dict` assigns a numerical rank to each two-card combination, influencing the bot's actions before the flop.

*   **Construction:** The dictionary categorizes hands as suited ("s") or offsuit ("o") and ranks them based on their potential strength in Texas Hold'em. Hands like "AAo" have a rank of 1, while weaker hands have higher numerical ranks.
*   **Normalization:** The `categorize_cards` function standardizes the hand representation (e.g., converting both "AK" and "KA" to "AK") to ensure consistent dictionary lookups.
*   **Limitations:** The preflop ranges are very static, do not model any mixed strategies, nor do they account for the number of players involved.

```
self.preflop_dict = {'AAo':1,'KKo':2,'QQo':3,'JJo':4,'TTo':5,'99o':6,'88o':7,'AKs':8,...}
```

### 3.2. Action Selection Logic

The `get_preflop_action` function determines the bot's action based on its hand ranking, position (small blind or big blind), and the actions of its opponent.

*   **Small Blind (Aggressive Opening):**
    *   The bot opens aggressively (raises) with hands ranked 1-25 in the dictionary, indicating premium hands. The exact range can be modified through the `small_blind_raise` parameter, allowing the bot to steal blinds.
    *   Raises are sized relative to the pot (`3 * pot` for very strong hands, `2 * pot` for moderately strong hands).
*   **Big Blind (Defensive Strategy):**
    *   The bot defends more liberally in the big blind, calling or raising with a wider range of hands depending on the opponent's initial bet size (`opp_pip`).
    *   The bot will call if the hand ranks highly, especially in contrast with the opponent's bet size. The bot also adds a random chance of calling.
*   **Facing Raises:**
    *   The bot uses a wider range of hands based on pot odds, which enables it to profitably defend against steal attempts.

### 3.3. Code Snippets

```
def get_preflop_action(self, cards, round_state, active):
    legal_actions = round_state.legal_actions()
    # Example: Raising with strong hands in the small blind
    if not big_blind and self.times_bet_preflop == 0:
        if self.preflop_dict[new_cards] in range(1, 26):
            self.times_bet_preflop += 1
            my_bet = 3 * pot
            return RaiseAction(self.no_illegal_raises(my_bet, round_state))
```

### 3.4. Potential Improvements

*   **Dynamic Ranges:** Implement dynamic ranges that adjust based on opponent tendencies and game conditions.
*   **Mixed Strategies:** Incorporate mixed strategies (randomly selecting different actions with certain probabilities) to avoid predictability.
*   **Stack Size Awareness:** Adjust preflop ranges based on stack sizes.

## 4. Auction Bidding Strategy: In-Depth Examination

The auction phase is a critical component of the game, and Goggins employs a complex strategy to determine its bid.

### 4.1. Hand Strength Evaluation

The `auction_strength` function uses Monte Carlo simulations to estimate the bot's hand strength with and without the auction card.

*   **Metrics:** The bot calculates `need_auction`, `win_without`, and `win_with` metrics.
    *   `need_auction`: The probability that the bot's hand needs the auction card to win against the opponent's hand.
    *   `win_without`: The probability that the bot's hand will win without the auction card.
    *   `win_with`: The probability that the bot's hand will win if the bot obtains the auction card.
*   **Monte Carlo Simulation:** The function simulates numerous game scenarios, drawing random cards to complete the board and evaluating the resulting hand strengths.
*   **Efficiency:** The `trials` parameter controls the number of simulations, balancing accuracy with computational cost.
*   **Improvement Considerations:** The model does not include modeling the hand strength of opponents and has multiple hard coded factors that relies on the number 3. It might be valuable to consider stack sizes more when bidding.

### 4.2. Bidding Logic

The `decide_action_auction` method determines the bid amount based on the hand strength metrics and game state.

*   **Aggressive Bidding:** The bot bids aggressively when `win_without` is low (≤ 0.2) or `win_with` is less than 0.6.
*   **Conservative Bidding:** If the bot has a strong hand even without the auction (`win_without` > 0.8), it makes a smaller bid.
*   **Adaptive Bidding:** The bot attempts to adapt to the opponent's bidding patterns by adjusting its bids based on the opponent's average bid amount (`self.add_auction`).

### 4.3. Code Snippets

```
def decide_action_auction(self, auction_strength, my_stack, pot):
    need_auction, win_without, win_with = auction_strength
    # Example: Bidding aggressively when needing the auction card
    if win_without <= 0.2 or win_with < 0.6:
        bid_amount = int(self.auction_factor * need_auction * pot * 3 + self.add_auction)
        bid_amount = max(bid_amount, int(self.add_auction * 3/2 * random.uniform(0.95, 1.05)))
        return BidAction(min(my_stack - 1, bid_amount))
```

### 4.4. Potential Improvements

*   **Bayesian Approach:** Implement a Bayesian model to update hand strength estimates based on the opponent's bidding behavior.
*   **Bid Sizing Optimization:** Refine bid sizing to maximize expected value, considering factors like opponent tendencies and stack sizes.
*   **Risk Assessment:** Assess the risk of losing the auction and adjust bids accordingly.

## 5. Postflop Strategy: Detailed Examination

The postflop strategy is where Goggins demonstrates its ability to adapt to changing game conditions and make informed decisions.

### 5.1. Hand Strength Evaluation

The `hand_strength` function estimates the bot's hand strength using Monte Carlo simulation. It leverages `eval7` library's optimized Monte Carlo equity function, but can fallback to the manual simulation if there is a failure.

*   **Monte Carlo Simulation:** The function simulates numerous game scenarios, drawing random cards to complete the board and evaluating the resulting hand strengths.
*   **Efficiency:** The `trials` parameter controls the number of simulations, balancing accuracy with computational cost.
*   **Limitations:** Doesn't factor in board texture.
*   **Draw Identification:** Currently identifies draw by the numeric value of the best hand, rather than an independent simulation.

### 5.2. Opponent Modeling

The bot tracks opponent aggression (`num_opp_bets`), pot bet frequency (`num_opp_potbets`), and bluffing tendencies (`opp_check_bluffs`).

*   **Metrics:** These metrics are updated in the `update_opponent_model` method and used to calculate `agg_rate`, `potbet_ratio`, and `bluff_rate`.
*   **Adaptation:** The bot adapts to these metrics by adjusting its calling frequency and bluffing frequency based on the opponent's perceived aggression and bluffing tendencies.
*   **Limitations:** Metrics are calculated based on the current or previous round only.

### 5.3. Decision-Making

The `decide_action_postflop` function determines the bot's action (check, raise, call, or fold) based on its hand strength, opponent model, and pot odds.

*   **Check/Raise:** The bot checks when it has a strong hand and believes the opponent is likely to bluff.
*   **Calling/Folding:** The bot calls or folds based on pot equity, hand strength, and opponent aggression.
*   **Bluffing:** The bot bluffs when the opponent checks multiple times.
*   **Improvement Considerations:** Could use longer term opponent memory.

### 5.4. Code Snippets

```
def decide_action_postflop(self, round_state, hand_strength, active):
    # Example: Check-raising when the opponent is likely to bluff
    if CheckAction in legal_actions:  # Check or raise branch
        if self.opp_check_bluffing and hand_strength > 0.75 and street != 5:
            self.check += 1
            self.my_checks += 1
            return CheckAction, None
```

### 5.5. Potential Improvements

*   **Range Analysis:** Implement range analysis to make more informed decisions about the bot's own hand strength and the likely hands of its opponents.
*   **Board Texture Analysis:** Analyze board texture to identify favorable and unfavorable boards for the bot's hand.
*   **Advanced Opponent Modeling:** Incorporate more sophisticated opponent modeling techniques, such as clustering opponents into different playing styles.

## 6. Opponent Modeling: Detailed Breakdown

The opponent modeling system is designed to track and exploit opponent tendencies.

### 6.1. Tracked Metrics

*   `num_opp_bets`: Number of times the opponent has bet.
*   `num_opp_potbets`: Number of times the opponent has made a pot-sized bet (defined as > 80% of the pot).
*   `opp_check_bluffs`: Number of times the opponent has bet after the bot has checked.

### 6.2. Adaptation

The bot adapts to these metrics by adjusting its calling frequency and bluffing frequency based on the opponent's perceived aggression and bluffing tendencies.

### 6.3. Limitations

*   The opponent model is relatively basic and could be improved by incorporating more advanced statistics, such as bet sizing patterns, fold frequencies, and hand range analysis.
*   The model's memory is limited, as it only considers the current round and the previous round when making decisions.

### 6.4. Potential Improvements

*   **Bet Sizing Patterns:** Track the opponent's bet sizing patterns to infer their hand strength.
*   **Fold Frequencies:** Track how often the opponent folds to bets and raises.
*   **Longer Term Memory:** Extend the model's memory to consider more historical data.

## 7. Adaptive Elements: In-Depth Review

Goggins incorporates several adaptive elements to respond to changing game dynamics.

### 7.1. Bankroll Management

The bot switches to more conservative play when its bankroll exceeds a certain threshold (`self.already_won`), securing wins.

### 7.2. Time Management

The bot decreases its simulation trials (`self.trials`) when the game clock is low, optimizing speed.

### 7.3. Opponent Exploitation

The bot identifies and attempts to exploit opponent tendencies, such as check-raising frequency, bluffing frequency, and auction bidding patterns.

## 8. Getting Started

To run Goggins, follow these steps:

1.  **Install Dependencies:**
    ```
    pip install eval7
    ```
2.  **MIT Engine:**
    ```
    Use MIT's engine https://github.com/mitpokerbots/engine-2025
    ```
3.  **Run the Bot:**
    ```
    python skeleton/runner.py -b player.py
    ```
