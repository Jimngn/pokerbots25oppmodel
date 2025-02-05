'''
Derived from MIT'S: FINAL BOT

'''
from skeleton.actions import FoldAction, CallAction, CheckAction, RaiseAction, BidAction
from skeleton.states import GameState, TerminalState, RoundState
from skeleton.states import NUM_ROUNDS, STARTING_STACK, BIG_BLIND, SMALL_BLIND
from skeleton.bot import Bot
from skeleton.runner import parse_args, run_bot
import random
import eval7, pprint

class Player(Bot):
    '''
    A pokerbot.
    '''

    def __init__(self):
        '''
        Called when a new game starts. Called exactly once.

        Arguments:
        Nothing.

        Returns:
        Nothing.
        '''
        self.preflop_dict = {'AAo':1,'KKo':2,'QQo':3,'JJo':4,'TTo':5,'99o':6,'88o':7,'AKs':8,'77o':9,'AQs':10,'AJs':11,'AKo':12,'ATs':13,
                             'AQo':14,'AJo':15,'KQs':16,'KJs':17,'A9s':18,'ATo':19,'66o':20,'A8s':21,'KTs':22,'KQo':23,'A7s':24,'A9o':25,'KJo':26,
                             '55o':27,'QJs':28,'K9s':29,'A5s':30,'A6s':31,'A8o':32,'KTo':33,'QTs':34,'A4s':35,'A7o':36,'K8s':37,'A3s':38,'QJo':39,
                             'K9o':40,'A5o':41,'A6o':42,'Q9s':43,'K7s':44,'JTs':45,'A2s':46,'QTo':47,'44o':48,'A4o':49,'K6s':50,'K8o':51,'Q8s':52,
                             'A3o':53,'K5s':54,'J9s':55,'Q9o':56,'JTo':57,'K7o':58,'A2o':59,'K4s':60,'Q7s':61,'K6o':62,'K3s':63,'T9s':64,'J8s':65,
                             '33o':66,'Q6s':67,'Q8o':68,'K5o':69,'J9o':70,'K2s':71,'Q5s':72,'T8s':73,'K4o':74,'J7s':75,'Q4s':76,'Q7o':77,'T9o':78,
                             'J8o':79,'K3o':80,'Q6o':81,'Q3s':82,'98s':83,'T7s':84,'J6s':85,'K2o':86,'22o':87,'Q2s':87,'Q5o':89,'J5s':90,'T8o':91,
                             'J7o':92,'Q4o':93,'97s':80,'J4s':95,'T6s':96,'J3s':97,'Q3o':98,'98o':99,'87s':75,'T7o':101,'J6o':102,'96s':103,'J2s':104,
                             'Q2o':105,'T5s':106,'J5o':107,'T4s':108,'97o':109,'86s':110,'J4o':111,'T6o':112,'95s':113,'T3s':114,'76s':80,'J3o':116,'87o':117,
                             'T2s':118,'85s':119,'96o':120,'J2o':121,'T5o':122,'94s':123,'75s':124,'T4o':125,'93s':126,'86o':127,'65s':128,'84s':129,'95o':130,
                             '53s':131,'92s':132,'76o':133,'74s':134,'65o':135,'54s':87,'85o':137,'64s':138,'83s':139,'43s':140,'75o':141,'82s':142,'73s':143,
                             '93o':144,'T2o':145,'T3o':146,'63s':147,'84o':148,'92o':149,'94o':150,'74o':151,'72s':152,'54o':153,'64o':154,'52s':155,'62s':156,
                             '83o':157,'42s':158,'82o':159,'73o':160,'53o':161,'63o':162,'32s':163,'43o':164,'72o':165,'52o':166,'62o':167,'42o':168,'32o':169,
                             }
        
        self.trials = 125
        self.total_rounds = 0
        self.already_won = False
        self.nit = 0
        #Playing like a nit works so :V
        self.opp_aggressive = False

        self.switched_to_100 = False
        self.switched_to_50 = False
    
        self.num_auctions_seen = 0
        self.my_total_bid = 0
        self.opp_total_bid = 0
        self.auction_factor = 1
        self.add_auction = 0

        self.small_blind_raise = 88
        self.big_blind_raise = 32
        self.big_blind_call = 88

        self.bluffed_this_round = False
        self.num_opp_potbets = 0
        self.num_opp_bets = 0

        self.raise_fact = 0.2
        self.reraise_fact = 0.025

        self.bluff_pm = 0

        self.bluffed_pm = 0
        self.bluff_numwins = 0
        self.bluff_numlosses = 0

        self.twobluff_pm = 0
        self.twonumwins = 0
        self.twonumlosses = 0

        self.onebluff_pm = 0
        self.onenumwins = 0
        self.onenumlosses = 0

        self.twobluff_fact = 1
        self.twobluff_not_working = False
        self.onebluff_fact = 1
        self.onebluff_not_working = False
        self.bluff_fact = 1
        self.bluff_not_working = 1
        self.draw_bluff_fact = 1
        self.draw_bluff_games = 0
        self.draw_bluff_losses = 0
        self.draw_bluff_pm = 0
        self.draw_bluff_this_round = False
        
        self.try_bluff = 1

        self.three_card_win = 0
        self.three_card_bet = 0
        self.check = 0
        self.opp_check_bluffs = 0
        self.opp_check_bluffing = False

        self.opp_checks = 0
        self.my_checks = 0
        self.last_cont = 0
        self.opp_check_bluff_this_round = False

        self.opp_auction_wins = 0
        self.opp_auction_bets = 0
        self.opp_auction_bluffing = False

        self.less_nit_call = False
        self.less_nit_call_pm = 0
        self.less_nit_call_losses = 0

        self.unnit_not_working = False
        # And if it doesn't work, just stop using it

        # Initialize opponent modeling dictionary
        self.opp_model = {}

    def update_opponent_model(self):
        '''
        Update opponent modeling statistics based on observed patterns.
        
        This is the main opponent model part
        
        3 parameters just based on the opponent is playing so we can adjust our strat
        
        Agg rate is just how many bets opp have done over rounds
        
        Similar with potbet and bluff rate. Just helps us quantify these metrics abit more. 
        
        '''
        rounds = self.total_rounds if self.total_rounds > 0 else 1
        agg_rate = self.num_opp_bets / rounds
        potbet_ratio = self.num_opp_potbets / (self.num_opp_bets + 1)
        bluff_rate = self.opp_check_bluffs / (self.check + 1) if self.check > 0 else 0
        self.opp_model = {
            "agg_rate": agg_rate,
            "potbet_ratio": potbet_ratio,
            "bluff_rate": bluff_rate
        }

    def handle_new_round(self, game_state, round_state, active):
        '''
        Called when a new round starts. Called NUM_ROUNDS times.

        Arguments:
        game_state: the GameState object.
        round_state: the RoundState object.
        active: your player's index.

        Returns:
        Nothing.
        '''
        my_bankroll = game_state.bankroll  # the total chips gained or lost so far
        game_clock = game_state.game_clock  # remaining seconds for the game
        round_num = game_state.round_num  # round number from 1 to NUM_ROUNDS
        big_blind = bool(active)
        self.opp_checks = 0
        self.my_checks = 0
        self.last_cont = 0
        self.opp_check_bluff_this_round = False
        
        self.opp_won_auction = False
        self.opp_auction_bet_this_round = False
        self.less_nit_call = False

        self.times_bet_preflop = 0
        self.bluffed_this_round = False
        self.twocheck = False
        self.onecheck = False
        self.bluff = False
        self.draw_hit = 0
        self.draw_hit_pct = 0

        self.draw_bluff_this_round = False

        if my_bankroll > 600:
            self.try_bluff = 1/4
        else:
            self.try_bluff = 1

        if self.bluff_not_working == 1:
            self.bluff_fact = 1
        elif self.bluff_not_working == 2:
            self.bluff_fact = 2
        else:
            self.bluff_fact = 1/6

        if not self.twobluff_not_working:
            self.twobluff_fact = 1
        else:
            self.twobluff_fact = 1/6

        if not self.onebluff_not_working:
            self.onebluff_fact = 1
        else:
            self.onebluff_fact = 1/6

        bankroll_threshold = int(1.5*(NUM_ROUNDS-round_num+1))
        if big_blind and (NUM_ROUNDS-round_num+1) % 2 == 1:
            bankroll_threshold += 1

        if my_bankroll > bankroll_threshold:
            self.already_won = True

        if game_clock < 20 and round_num <= 333 and not self.switched_to_100:
            self.trials = 100
            self.switched_to_100 = True
            self.nit = 0.03
        elif game_clock < 10 and round_num <= 666 and not self.switched_to_50:
            self.trials = 50
            self.switched_to_50 = True
            self.nit = 0.06

        if self.draw_bluff_losses >= 3 and self.draw_bluff_pm < -69:
            self.draw_bluff_fact = 1/4
        else:
            self.draw_bluff_fact = 1

    def handle_round_over(self, game_state, terminal_state, active):
        '''
        Called when a round ends. Called NUM_ROUNDS times.

        Arguments:
        game_state: the GameState object.
        terminal_state: the TerminalState object.
        active: your player's index.

        Returns:
        Nothing.
        '''
        my_delta = terminal_state.deltas[active]
        previous_state = terminal_state.previous_state
        street = previous_state.street

        if self.less_nit_call:
            if my_delta < 0:
                self.less_nit_call_losses += 1
            self.less_nit_call_pm += my_delta

        if self.less_nit_call_losses >= 3 and self.less_nit_call_pm < -69:
            self.unnit_not_working = True
        else:
            self.unnit_not_working = False

        self.total_rounds += 1

        if game_state.round_num == NUM_ROUNDS:
            print(game_state.game_clock)
            print(f'num opp bets {self.num_opp_bets}')
            print(f'num opp 80%: {self.num_opp_potbets}')
            print(f'bluff pm: {self.bluff_pm}')
            print(f'normal bluff pm: {self.bluffed_pm}')
            print(f'normal bluff wins: {self.bluff_numwins}')
            print(f'normal bluff losses: {self.bluff_numlosses}')
            print(f'two check bluff pm: {self.twobluff_pm}')
            print(f'two check wins: {self.twonumwins}')
            print(f'two check losses: {self.twonumlosses}')
            print(f'one check bluff pm: {self.onebluff_pm}')
            print(f'one check wins: {self.onenumwins}')
            print(f'one check losses: {self.onenumlosses}')
            print(f'checks {self.check}')
            print(f'opp check bets {self.opp_check_bluffs}')
            print(f'opp auction wins {self.opp_auction_wins}')
            print(f'opp auction flop bets {self.opp_auction_bets}')
            print(f'draw bluffs {self.draw_bluff_games}')
            print(f'draw losses {self.draw_bluff_losses}')
            print(f'draw pm {self.draw_bluff_pm}')

        if self.draw_bluff_this_round:
            self.draw_bluff_pm += my_delta
            self.draw_bluff_games += 1
            if my_delta < 0:
                self.draw_bluff_losses += 1
            

        if self.num_opp_bets >= 25 and (self.num_opp_potbets / self.num_opp_bets > 0.4):
            self.opp_aggressive = True
        else:
            self.opp_aggressive = False

        if self.opp_won_auction:
            self.opp_auction_wins += 1

        if (self.check >= 8) and (self.opp_check_bluffs / self.check >= 0.7):
            self.opp_check_bluffing = True
        else:
            self.opp_check_bluffing = False

        if (self.opp_auction_wins >= 10) and (self.opp_auction_bets / self.opp_auction_wins >= 0.7):
            self.opp_auction_bluffing = True
        else:
            self.opp_auction_bluffing = False

        if self.bluffed_this_round:
            if abs(my_delta) != 400:
                self.bluff_pm += my_delta

        if self.bluff:
            self.bluffed_pm += my_delta
            if my_delta > 0:
                self.bluff_numwins += 1
            else:
                self.bluff_numlosses += 1
            if ((self.bluff_numwins + self.bluff_numlosses >= 5) and (self.bluff_numlosses / (self.bluff_numwins + self.bluff_numlosses) >= 0.2) and self.bluffed_pm < 0) or (self.bluffed_pm < -250):
                self.bluff_not_working = 0
            elif (self.bluff_numwins + self.bluff_numlosses >= 5) and (self.bluff_numlosses / (self.bluff_numwins + self.bluff_numlosses) <= 0.15) and self.bluffed_pm > 0:
                self.bluff_not_working = 2
            else:
                self.bluff_not_working = 1

        elif self.twocheck:
            if abs(my_delta) != 400:
                self.twobluff_pm += my_delta
                if my_delta > 0:
                    self.twonumwins += 1
                else:
                    self.twonumlosses += 1
            if (not self.twobluff_not_working and (self.twonumwins + self.twonumlosses >= 8) and (self.twonumlosses / (self.twonumwins + self.twonumlosses) >= 0.3) and self.twobluff_pm < 0) or self.twobluff_pm < -250:
                self.twobluff_not_working = True

        elif self.onecheck:
            if abs(my_delta) != 400:
                self.onebluff_pm += my_delta
                if my_delta > 0:
                    self.onenumwins += 1
                else:
                    self.onenumlosses += 1
            if not self.onebluff_not_working and (self.onenumwins + self.onenumlosses >= 8) and (self.onenumlosses / (self.onenumwins + self.onenumlosses) >= 0.3) and self.onebluff_pm < 0:
                self.onebluff_not_working = True

        if street >= 3:
            self.num_auctions_seen += 1
            my_bid = terminal_state.bids[active]
            opp_bid = terminal_state.bids[1-active]
            self.my_total_bid += my_bid
            self.opp_total_bid += opp_bid
            self.opp_total_bid = max(self.opp_total_bid, 1)
            if self.opp_total_bid / self.num_auctions_seen >= 70 and self.num_auctions_seen % 20 == 0:
                self.add_auction = 2/5 * self.opp_total_bid / self.num_auctions_seen

    def categorize_cards(self, cards):
        rank1 = cards[0][0]
        rank2 = cards[1][0]
        suit1 = cards[0][1]
        suit2 = cards[1][1]
        ranking = {'A': 0, 'K': 1, 'Q': 2, 'J': 3, 'T': 4, '9': 5, '8': 6, '7': 7, '6': 8, '5': 9, '4': 10, '3': 11, '2': 12}

        if ranking[rank1] < ranking[rank2]:
            hpair = rank1 + rank2
        else:
            hpair = rank2 + rank1
        
        onsuit = 's' if suit1 == suit2 else 'o'
        return hpair + onsuit

    def no_illegal_raises(self, bet, round_state):
        min_raise, max_raise = round_state.raise_bounds()        
        if bet >= max_raise:
            return max_raise
        else:
            return bet

    def get_preflop_action(self, cards, round_state, active):
        legal_actions = round_state.legal_actions()
        my_stack = round_state.stacks[active]
        opp_stack = round_state.stacks[1-active]
        my_contribution = STARTING_STACK - my_stack
        opp_contribution = STARTING_STACK - opp_stack
        opp_pip = round_state.pips[1-active]
        pot = my_contribution + opp_contribution
        big_blind = bool(active)
        new_cards = self.categorize_cards(cards)
        if not big_blind and self.times_bet_preflop == 0:
            if self.preflop_dict[new_cards] in range(1, 26):
                self.times_bet_preflop += 1
                my_bet = 3 * pot
                return RaiseAction(self.no_illegal_raises(my_bet, round_state))
            elif self.preflop_dict[new_cards] in range(20, self.small_blind_raise):
                self.times_bet_preflop += 1
                my_bet = 2 * pot
                return RaiseAction(self.no_illegal_raises(my_bet, round_state))
            else:
                return FoldAction()
        elif big_blind and self.times_bet_preflop == 0:
            if self.preflop_dict[new_cards] in range(1, 5) or (self.preflop_dict[new_cards] in range(5, self.big_blind_raise) and pot <= 20):
                self.times_bet_preflop += 1
                my_bet = 2 * pot
                if RaiseAction in legal_actions:
                    return RaiseAction(self.no_illegal_raises(my_bet, round_state))
                elif CallAction in legal_actions:
                    return CallAction()
                else:
                    print("this shouldn't ever happen")
            elif opp_pip == 2 and self.preflop_dict[new_cards] in range(1, 60) and random.random() < 0.69:
                self.times_bet_preflop += 1
                my_bet = 2 * pot
                if RaiseAction in legal_actions:
                    return RaiseAction(self.no_illegal_raises(my_bet, round_state))
                return CheckAction()
            elif self.preflop_dict[new_cards] in range(5, int(self.big_blind_call + 1 - ((opp_pip - 2) / 198) ** (1 / 3) * (self.big_blind_call + 1 - 5))) and opp_pip <= 200:
                if CallAction in legal_actions:
                    return CallAction()
                else:
                    return CheckAction()
            else:
                if CheckAction in legal_actions:
                    return CheckAction()
                return FoldAction()
        else:
            if self.preflop_dict[new_cards] in range(1, 5):
                self.times_bet_preflop += 1
                my_bet = 2 * pot
                if RaiseAction in legal_actions:
                    return RaiseAction(self.no_illegal_raises(my_bet, round_state))
                elif CallAction in legal_actions:
                    return CallAction()
                else:
                    print("this shouldn't ever happen")
            elif self.preflop_dict[new_cards] in range(5, int(67 - ((opp_pip - 2) / 398) ** (1 / 3) * 61)):
                if CallAction in legal_actions:
                    return CallAction()
                else:
                    return CheckAction()
            else:
                if CheckAction in legal_actions:
                    return CheckAction()
                return FoldAction()

    def auction_strength(self, round_state, street, active):
        board = [eval7.Card(board_card) for board_card in round_state.deck[:street]]
        my_hole = [eval7.Card(my_card) for my_card in round_state.hands[active]]
        comb = board + my_hole
        num_more_board = 5 - len(board)
        opp_num = 2
        auction_num = 1

        deck = eval7.Deck()
        for card in comb:
            deck.cards.remove(card)

        num_need_auction = 0
        num_win_without_auction = 0
        num_win_with_auction = 0
        trials = 0

        while trials < self.trials:
            deck.shuffle()
            cards = deck.peek(num_more_board + opp_num + auction_num)
            opp_hole = cards[:opp_num]
            board_rest = cards[opp_num:len(cards) - 1]
            auction_card = [cards[-1]]

            my_auc_val = eval7.evaluate(my_hole + board + board_rest + auction_card)
            opp_no_auc_val = eval7.evaluate(opp_hole + board + board_rest)
            my_no_auc_val = eval7.evaluate(my_hole + board + board_rest)
            opp_auc_val = eval7.evaluate(opp_hole + board + board_rest + auction_card)

            if my_auc_val > opp_no_auc_val and my_no_auc_val < opp_auc_val:
                num_need_auction += 1
            if my_no_auc_val > opp_auc_val:
                num_win_without_auction += 1
            if my_auc_val > opp_no_auc_val:
                num_win_with_auction += 1

            trials += 1

        need_auction = num_need_auction / trials
        win_without = num_win_without_auction / trials
        win_with = num_win_with_auction / trials

        return need_auction, win_without, win_with

    def decide_action_auction(self, auction_strength, my_stack, pot):
        need_auction, win_without, win_with = auction_strength
        hand_strength = (win_without + win_with) / 2
        # Adjust hand strength based on opponent model
        if self.opp_model:
            hand_strength = hand_strength - 0.05 * self.opp_model.get("agg_rate", 0) + 0.03 * self.opp_model.get("bluff_rate", 0)

        if my_stack == 0:
            return BidAction(0)
        elif my_stack == 1:
            return BidAction(1)

        if win_without <= 0.2 or win_with < 0.6:
            bid_amount = int(self.auction_factor * need_auction * pot * 3 + self.add_auction)
            bid_amount = max(bid_amount, int(self.add_auction * 3/2 * random.uniform(0.95, 1.05)))
            return BidAction(min(my_stack - 1, bid_amount))
        elif win_without > 0.8:
            rand_val = 4 * random.random() + 1
            factor = 0.7 if pot < 40 else 0.6
            bid_amount = int(pot * factor + rand_val + self.add_auction)
            bid_amount = max(bid_amount, int(self.add_auction * 3/2 * random.uniform(0.95, 1.05)))
            return BidAction(min(my_stack - 1, bid_amount))
        elif win_without <= 0.8 and win_without > 0.6:
            bid_amount = int(self.auction_factor * need_auction * pot * 2 + self.add_auction)
            bid_amount = max(bid_amount, int(self.add_auction * 3/2 * random.uniform(0.95, 1.05)))
            return BidAction(min(my_stack - 1, bid_amount))
        elif win_without <= 0.6 and win_without > 0.2:
            if pot <= 40:
                bid_amount = int(self.auction_factor * need_auction * pot * 7 + self.add_auction)
            else:
                bid_amount = int(self.auction_factor * (hand_strength ** 2) * need_auction * pot * 10 + self.add_auction)
            bid_amount = max(bid_amount, int(self.add_auction * 3/2 * random.uniform(0.95, 1.05)))
            return BidAction(min(my_stack - 1, bid_amount))
        else:
            print("this shouldn't ever happen")
            return BidAction(0)

    def decide_action_postflop(self, round_state, hand_strength, active):
        legal_actions = round_state.legal_actions()
        street = round_state.street
        my_pip = round_state.pips[active]
        opp_pip = round_state.pips[1-active]
        my_stack = round_state.stacks[active]
        opp_stack = round_state.stacks[1-active]
        my_bid = round_state.bids[active]
        opp_bid = round_state.bids[1-active]
        my_contribution = STARTING_STACK - my_stack
        opp_contribution = STARTING_STACK - opp_stack
        pot = my_contribution + opp_contribution
        big_blind = bool(active)
        num_cards = len(round_state.hands[active])
        unnit = 0

        if street == 3 and opp_bid > my_bid:
            self.opp_won_auction = True

        if opp_pip > 0:
            if self.my_checks > 0:
                self.opp_check_bluffs += 1
                self.opp_check_bluff_this_round = True
            if street == 3 and self.opp_won_auction:
                self.opp_auction_bets += 1
                self.opp_auction_bet_this_round = True
            if my_pip > 0:
                self.bluffed_this_round = True
            self.num_opp_bets += 1
            self.opp_checks = 0
            self.last_cont = opp_contribution
        elif big_blind and street > 3:
            if opp_contribution == self.last_cont:
                self.opp_checks += 1
        elif not big_blind and opp_pip == 0:
            self.opp_checks += 1

        if opp_pip > 0.8 * (pot - opp_pip + my_pip):
            self.num_opp_potbets += 1

        rand = random.random()
        if CheckAction in legal_actions:  # Check or raise branch
            if self.opp_check_bluffing and hand_strength > 0.75 and street != 5:
                self.check += 1
                self.my_checks += 1
                return CheckAction, None
            if rand < hand_strength + 0.15 and hand_strength >= (0.5 + ((street % 3) * self.raise_fact)):
                self.my_checks = 0
                self.opp_checks = 0
                return RaiseAction, 1
            elif street == 5 and hand_strength > 0.9:
                self.my_checks = 0
                self.opp_checks = 0
                return RaiseAction, 1
            elif self.draw_hit_pct > 0.25 and hand_strength >= 0.4 and street != 5 and not self.bluffed_this_round and rand <= self.draw_bluff_fact:
                self.my_checks = 0
                self.opp_checks = 0
                self.bluffed_this_round = True
                self.draw_bluff_this_round = True
                return RaiseAction, 0
            elif self.opp_checks == 3 and rand < 0.8:
                return RaiseAction, 0
            elif not self.bluffed_this_round and not big_blind and (self.opp_checks == 2) and (rand < 0.869 * self.try_bluff * self.twobluff_fact):
                self.opp_checks = 0
                self.bluffed_this_round = True
                self.twocheck = True
                self.my_checks = 0
                return RaiseAction, 0
            elif not self.bluffed_this_round and big_blind and (self.opp_checks == 2) and (rand < self.try_bluff * 0.69 * self.twobluff_fact):
                self.opp_checks = 0
                self.bluffed_this_round = True
                self.twocheck = True
                self.my_checks = 0
                return RaiseAction, 0
            elif not self.bluffed_this_round and not big_blind and (self.opp_checks == 1) and (rand < self.try_bluff * 0.25 * self.onebluff_fact):
                self.opp_checks = 0
                self.bluffed_this_round = True
                self.onecheck = True
                self.my_checks = 0
                return RaiseAction, 0
            elif not self.less_nit_call and not self.bluffed_this_round and (my_bid > opp_bid) and (rand < (self.try_bluff * self.bluff_fact * (1 - hand_strength) / (1 + (street % 3)))) and (hand_strength < 0.65):
                self.opp_checks = 0
                self.bluffed_this_round = True
                self.bluff = True
                self.my_checks = 0
                return RaiseAction, 0
            self.check += 1
            self.my_checks += 1
            return CheckAction, None
        else:  # Fold, Call, or Raise branch
            pot_equity = (opp_pip - my_pip) / (pot - (opp_pip - my_pip))
            if pot_equity > 0.7 and pot_equity < 0.8:
                pot_equity = 0.7
            elif pot_equity >= 0.8 and pot_equity < 1.1:
                pot_equity = 0.8
            elif pot_equity >= 1.1:
                pot_equity = 0.85
            elif pot_equity <= 0.75:
                pot_equity = min(pot_equity + 0.0725, 0.725)
            if pot_equity <= 0.5:
                pot_equity = min(pot_equity + 0.0725, 0.5)
            if self.opp_aggressive and pot_equity >= 0.8 and my_pip == 0:
                if num_cards == 2:
                    unnit += 0.1
                else:
                    unnit += 0.05
            if self.opp_auction_bluffing and self.opp_auction_bet_this_round:
                if self.opp_aggressive and ((opp_pip - my_pip) / (pot - (opp_pip - my_pip)) > 0.8):
                    unnit += 0.15
                elif not self.opp_aggressive:
                    unnit += 0.1
            elif self.opp_check_bluffing and self.opp_check_bluff_this_round:
                if self.opp_aggressive and ((opp_pip - my_pip) / (pot - (opp_pip - my_pip)) > 0.8):
                    if num_cards == 2:
                        unnit += 0.1
                    else:
                        unnit += 0.05
                elif not self.opp_aggressive and num_cards == 2:
                    unnit += 0.075

            # Incorporate opponent model adjustments
            risk_adjustment = 0
            if self.opp_model.get("agg_rate", 0) > 1.0:
                risk_adjustment += 0.05
            if self.opp_model.get("potbet_ratio", 0) > 0.5:
                risk_adjustment += 0.05
            if self.opp_model.get("bluff_rate", 0) > 0.5:
                risk_adjustment -= 0.05
            pot_equity -= risk_adjustment

            if hand_strength > pot_equity and hand_strength < pot_equity + unnit and hand_strength > 0.35:
                self.less_nit_call = True
            self.my_checks = 0
            self.opp_check_bluff_this_round = False
            self.opp_auction_bet_this_round = False
            if hand_strength < pot_equity:
                return FoldAction, None
            elif hand_strength < 0.35:
                return FoldAction, None
            else:
                reraise_strength = (0.9 + ((street % 3) * self.reraise_fact))
                if not self.opp_check_bluff_this_round and (hand_strength > reraise_strength) or (hand_strength - pot_equity > 0.3 and hand_strength > (reraise_strength - 0.05)):
                    return RaiseAction, 1
                return CallAction, None

    def hand_strength(self, round_state, street, active):
        '''
        Additional use of eval7 library here. 
        https://pypi.org/project/eval7/#description
        
        Equity calculation functions using monte carlo simulation
        
        #Maybe try to use py_hand_vs_range_exact to see if the results becomes more consistent
        
        Calculate hand strength using eval7's optimized Monte Carlo equity function if available;
        otherwise, fallback to the manual simulation.
        '''
        board = [eval7.Card(x) for x in round_state.deck[:street]]
        my_hole = [eval7.Card(x) for x in round_state.hands[active]]
        if street > 0:
            try:
                equity = eval7.py_hand_vs_range_monte_carlo(my_hole, board, trials=self.trials)
                self.draw_hit_pct = 0
                return equity
            except Exception as e:
                return self.manual_hand_strength(round_state, street, active)
        else:
            cards = self.categorize_cards(round_state.hands[active])
            return 1.0 - (self.preflop_dict.get(cards, 170) / 170.0)

    def manual_hand_strength(self, round_state, street, active):
        '''
        Fallback manual Monte Carlo simulation for hand strength evaluation.
        Retains the original simulation functionality.
        '''
        board = [eval7.Card(x) for x in round_state.deck[:street]]
        my_hole = [eval7.Card(x) for x in round_state.hands[active]]
        comb = board + my_hole
        num_more_board = 5 - len(board)
        legal_actions = round_state.legal_actions()
        if len(my_hole) == 2 and street > 0 and (BidAction not in legal_actions):
            opp_num = 3
        elif len(my_hole) == 3 and street > 0 and (round_state.bids[active] == round_state.bids[1-active]):
            opp_num = 3
        else:
            opp_num = 2
        deck = eval7.Deck()
        for card in comb:
            deck.cards.remove(card)
        num_better = 0
        trials = 0
        draw_hit = 0
        while trials < self.trials:
            deck.shuffle()
            cards = deck.peek(opp_num + num_more_board)
            opp_hole = cards[:opp_num]
            board_rest = cards[opp_num:]
            my_val = eval7.evaluate(my_hole + board + board_rest)
            opp_val = eval7.evaluate(opp_hole + board + board_rest)
            if my_val > opp_val:
                num_better += 2
            elif my_val == opp_val:
                num_better += 1
            trials += 1
            if 67305472 <= my_val <= 84715911:
                draw_hit += 1
        self.draw_hit_pct = draw_hit / trials if trials > 0 else 0
        return num_better / (2 * trials)

    def get_action(self, game_state, round_state, active):
        '''
        Where the magic happens - your code should implement this function.
        Called any time the engine needs an action from your bot.

        Arguments:
        game_state: the GameState object.
        round_state: the RoundState object.
        active: your player's index.

        Returns:
        Your action.
        '''
        legal_actions = round_state.legal_actions()
        street = round_state.street
        my_cards = round_state.hands[active]
        my_pip = round_state.pips[active]
        opp_pip = round_state.pips[1-active]
        my_stack = round_state.stacks[active]
        opp_stack = round_state.stacks[1-active]
        my_bid = round_state.bids[active]
        opp_bid = round_state.bids[1-active]
        my_contribution = STARTING_STACK - my_stack
        opp_contribution = STARTING_STACK - opp_stack
        self.draw_hit = 0
        self.draw_hit_pct = 0

        # Update opponent model based on observed patterns
        self.update_opponent_model()

        if self.already_won:
            if BidAction in legal_actions:
                return BidAction(0)
            elif CheckAction in legal_actions:
                return CheckAction()
            else:
                return FoldAction()

        pot = my_contribution + opp_contribution
        min_raise, max_raise = round_state.raise_bounds()
        hand_strength = self.hand_strength(round_state, street, active) - self.nit
        auction_strength = self.auction_strength(round_state, street, active)

        if my_contribution > 100:
            hand_strength -= 0.03

        if BidAction in legal_actions:
            return self.decide_action_auction(auction_strength, my_stack, pot)
        elif street == 0:
            return self.get_preflop_action(my_cards, round_state, active)
        else:
            if street == 3:
                self.last_cont = opp_contribution
            decision, conf = self.decide_action_postflop(round_state, hand_strength, active)

        rand = random.random()
        if decision == RaiseAction and RaiseAction in legal_actions:
            hand_strength_threshold = 0.8 + 0.05 * (street % 3)
            if conf != 0 and hand_strength < hand_strength_threshold:
                bet_max = int((1 + (2 * (hand_strength ** 2) * rand)) * 3 * pot / 8)
                maximum = min(max_raise, bet_max)
                minimum = max(min_raise, pot / 4)
            else:
                maximum = min(max_raise, 7 * pot / 4)
                minimum = max(min_raise, 1.10 * pot)
            if maximum <= minimum:
                amount = int(min_raise)
            else:
                amount = int(rand * (maximum - minimum) + minimum)
            return RaiseAction(amount)
        if decision == RaiseAction and RaiseAction not in legal_actions:
            if CallAction in legal_actions:
                return CallAction()
            self.check += 1
            self.my_checks += 1
            return CheckAction()
        return decision()

if __name__ == '__main__':
    run_bot(Player(), parse_args())

