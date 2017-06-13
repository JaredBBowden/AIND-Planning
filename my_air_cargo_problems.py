from aimacode.logic import PropKB
from aimacode.planning import Action
from aimacode.search import (
    Node, Problem,
)
from aimacode.utils import expr
from lp_utils import (
    FluentState, encode_state, decode_state,
)
from my_planning_graph import PlanningGraph

from functools import lru_cache


class AirCargoProblem(Problem):
    def __init__(self, cargos, planes, airports, initial: FluentState, goal: list):
        """

        :param cargos: list of str
            cargos in the problem
        :param planes: list of str
            planes in the problem
        :param airports: list of str
            airports in the problem
        :param initial: FluentState object
            positive and negative literal fluents (as expr) describing initial state
        :param goal: list of expr
            literal fluents required for goal test
        """
        self.state_map = initial.pos + initial.neg
        self.initial_state_TF = encode_state(initial, self.state_map)
        Problem.__init__(self, self.initial_state_TF, goal=goal)
        self.cargos = cargos
        self.planes = planes
        self.airports = airports
        self.actions_list = self.get_actions()

    def get_actions(self):
        """
        This method creates concrete actions (no variables) for all actions in the problem
        domain action schema and turns them into complete Action objects as defined in the
        aimacode.planning module. It is computationally expensive to call this method directly;
        however, it is called in the constructor and the results cached in the `actions_list` property.

        Returns:
        ----------
        list<Action>
            list of Action objects
        """

        # TODO create concrete Action objects based on the domain action schema for: Load, Unload, and Fly
        # concrete actions definition: specific literal action that does not include variables as with the schema
        # for example, the action schema 'Load(c, p, a)' can represent the concrete actions 'Load(C1, P1, SFO)'
        # or 'Load(C2, P2, JFK)'.  The actions for the planning problem must be concrete because the problems in
        # forward search and Planning Graphs must use Propositional Logic

        def load_actions():
            """Create all concrete Load actions and return a list

            :return: list of Action objects
            """

            # To hold load actions
            loads = []

            # General search-space cues: for each element of cargo, for every
            # plane, in every airport, consider the following LOAD actions:
            # Note: use element names from action schema:
            # Let c = cargo, p = plane, a = airport
            for c in self.cargos:
                for p in self.planes:
                    for a in self.airports:

                        # Specify preconditions for
                        # the load action. Note on functionality:
                        # [expr("At({}, {})".format("sure", "thing"))]
                        # Evaluates to:
                        # [At(sure, thing)]

                        # Specify preconditions:
                        # At(c, a) ∧ At(p, a) ∧ Cargo(c) ∧ Plane(p) ∧ Airport(a)
                        precond_pos = [expr("At({}, {})".format(c, a)),
                                       expr("At({}, {})".format(p, a))]

                        precond_neg = []

                        # Specify effects:
                        # ¬ At(c, a) ∧ In(c, p))
                        effect_rem = [expr("At({}, {})".format(c, a))]
                        effect_add = [expr("In({}, {})".format(c, p))]

                        # Specify the load action and add the above
                        # Load(c, p, a),

                        # FIXME Do I need to be consistent with how
                        # these lists are combined?
                        load = Action(expr("Load({}, {}, {})".format(c, p, a)), [precond_pos, precond_neg], [effect_add, effect_rem])

                        # Append these combinations to the full list
                        loads.append(load)

            return loads

        def unload_actions():
            """Create all concrete Unload actions and return a list

            :return: list of Action objects
            """

            # FIXME need to cover "At" and "In"
            # To hold unload actions
            unloads = []

            # As above -- for each element of cargo, for every
            # plane, in every airport, consider the following UNLOAD actions:
            # Note: use element names from action schema:
            # Let c = cargo, p = plane, a = airport
            for c in self.cargos:
                for p in self.planes:
                    for a in self.airports:

                        # Specify preconditions
                        # See comments in "load" (above) for a description of
                        # domain-specific functions.
                        # In(c, p) ∧ At(p, a) ∧ Cargo(c) ∧ Plane(p) ∧ Airport(a)
                        precond_pos = [expr("In({}, {})".format(c, p)),
                                       expr("At({}, {})".format(p, a))]

                        precond_neg = []

                        # Specify effects
                        # At(c, a) ∧ ¬ In(c, p))
                        effect_rem = [expr("In({}, {})".format(c, p))]
                        effect_add = [expr("At({}, {})".format(c, a))]

                        # Specify the unload action
                        # Unload(c, p, a)
                        unload = Action(expr("Unload({}, {}, {})".format(c, p, a)),
                                        [precond_pos, precond_neg],
                                        [effect_add, effect_rem])

                        # Append these combinations to the full list
                        unloads.append(unload)

            return unloads

        def fly_actions():
            """Create all concrete Fly actions and return a list

            :return: list of Action objects
            """
            flys = []
            for fr in self.airports:
                for to in self.airports:
                    if fr != to:
                        for p in self.planes:

                            # At(p, from) ∧ Plane(p) ∧ Airport(from) ∧ Airport(to)
                            precond_pos = [expr("At({}, {})".format(p, fr)),
                                           ]

                            precond_neg = []

                            # ¬ At(p, from) ∧ At(p, to))
                            effect_add = [expr("At({}, {})".format(p, to))]
                            effect_rem = [expr("At({}, {})".format(p, fr))]

                            # Fly(p, from, to)
                            fly = Action(expr("Fly({}, {}, {})".format(p, fr, to)),
                                         [precond_pos, precond_neg],
                                         [effect_add, effect_rem])

                            flys.append(fly)
            return flys


        # All of the possible combinations of states
        return load_actions() + unload_actions() + fly_actions()

    def actions(self, state: str) -> list:
        """ Return the actions that can be executed in the given state.

        :param state: str
            state represented as T/F string of mapped fluents (state variables)
            e.g. 'FTTTFF'
        :return: list of Action objects
        """
        # Note that the following control flow is adapted from the example
        # provided in ./example_have_cake.py

        # List to hold possible actions
        possible_actions = []

        # Implement the knowledge base class, imported from aimacode.logic
        kb = PropKB()
        kb.tell(decode_state(state, self.state_map).pos_sentence())

        # Iterate through actions in the action list and determine if
        # they are possible
        for action in self.actions_list:

            # Note Actions that are possible are True
            is_possible = True

            for clause in action.precond_pos:
                if clause not in kb.clauses:
                    is_possible = False

            for clause in action.precond_neg:
                if clause in kb.clauses:
                    is_possible = False

            if is_possible:
                possible_actions.append(action)

        return possible_actions

    def result(self, state: str, action: Action):
        """ Return the state that results from executing the given
        action in the given state. The action must be one of
        self.actions(state).

        :param state: state entering node
        :param action: Action applied
        :return: resulting state after action
        """

        # FIXME Again, this seems to just be the code from example_have_cake.
        new_state = FluentState([], [])

        old_state = decode_state(state, self.state_map)

        for fluent in old_state.pos:
            if fluent not in action.effect_rem:
                new_state.pos.append(fluent)

        for fluent in action.effect_add:
            if fluent not in new_state.pos:
                new_state.pos.append(fluent)

        for fluent in old_state.neg:
            if fluent not in action.effect_add:
                new_state.neg.append(fluent)

        for fluent in action.effect_rem:
            if fluent not in new_state.neg:
                new_state.neg.append(fluent)

        return encode_state(new_state, self.state_map)


    def goal_test(self, state: str) -> bool:
        """ Test the state to see if goal is reached

        :param state: str representing state
        :return: bool
        """
        kb = PropKB()
        kb.tell(decode_state(state, self.state_map).pos_sentence())
        for clause in self.goal:
            if clause not in kb.clauses:
                return False
        return True

    def h_1(self, node: Node):
        # note that this is not a true heuristic
        h_const = 1
        return h_const

    @lru_cache(maxsize=8192)
    def h_pg_levelsum(self, node: Node):
        """This heuristic uses a planning graph representation of the problem
        state space to estimate the sum of all actions that must be carried
        out from the current state in order to satisfy each individual goal
        condition.
        """
        # requires implemented PlanningGraph class
        pg = PlanningGraph(self, node.state)
        pg_levelsum = pg.h_levelsum()
        return pg_levelsum

    @lru_cache(maxsize=8192)
    def h_ignore_preconditions(self, node: Node):
        """This heuristic estimates the minimum number of actions that must be
        carried out from the current state in order to satisfy all of the goal
        conditions by ignoring the preconditions required for an action to be
        executed.
        """
        # TODO implement (see Russell-Norvig Ed-3 10.2.3  or Russell-Norvig Ed-2 11.2)

        # FIXME Remove after review
        # Review objects in the state_map. Check lp_utils
        # The first question here is: how many actions are possible in the
        # current state?

        # Implement the knowledge base class, imported from aimacode.logic,
        # and adapted from goal_test (above)
        # FIXME add node?
        kb = PropKB()
        kb.tell(decode_state(node.state, self.state_map).pos_sentence())

        # Counter for number of actions that fall within goal
        count = 0
        for clause in self.goal:
            if clause not in kb.clauses:
                count += 1

        return count

# FIXME Let's look at how the known example has been adapted before starting
# on the others

def air_cargo_p1() -> AirCargoProblem:
    cargos = ['C1', 'C2']
    planes = ['P1', 'P2']
    airports = ['JFK', 'SFO']
    pos = [expr('At(C1, SFO)'),
           expr('At(C2, JFK)'),

           # FIXME What's the deal with the trailing comma?
           expr('At(P1, SFO)'),
           expr('At(P2, JFK)'),
           ]

    neg = [expr('At(C2, SFO)'),
           expr('In(C2, P1)'),
           expr('In(C2, P2)'),

           expr('At(C1, JFK)'),
           expr('In(C1, P1)'),
           expr('In(C1, P2)'),

           expr('At(P1, JFK)'),
           expr('At(P2, SFO)'),
           ]

    init = FluentState(pos, neg)

    goal = [expr('At(C1, JFK)'),
            expr('At(C2, SFO)'),
            ]

    return AirCargoProblem(cargos, planes, airports, init, goal)


def air_cargo_p2() -> AirCargoProblem:
    # Relative to example p1:
    # Adding an additional cargo
    cargos = ["C1", "C2", "C3"]
    # Adding a plane
    planes = ["P1", "P2", "P3"]
    # Adding Atlanta
    airports = ["JFK", "SFO", "ATL"]

    # Initial states
    pos = [expr("At(C1, SFO)"),
           expr("At(C2, JFK)"),
           expr("At(C3, ATL)"),

           expr("At(P1, SFO)"),
           expr("At(P2, JFK)"),
           expr("At(P3, ATL)"),
           ]

    # Cover all of the negative states
    neg = [expr("At(C1, JFK)"),
           expr("At(C1, ATL)"),
           expr("In(C1, P1)"),
           expr("In(C1, P2)"),
           expr("In(C1, P3)"),

           expr("At(C2, SFO)"),
           expr("At(C2, ATL)"),
           expr("In(C2, P1)"),
           expr("In(C2, P2)"),
           expr("In(C2, P3)"),

           expr("At(C3, SFO)"),
           expr("At(C3, JFK)"),
           expr("In(C3, P1)"),
           expr("In(C3, P2)"),
           expr("In(C3, P3)"),

           expr("At(P1, JFK)"),
           expr("At(P1, ATL)"),

           expr("At(P2, SFO)"),
           expr("At(P2, ATL)"),

           expr("At(P3, SFO)"),
           expr("At(P3, JFK)"),
           ]

    init = FluentState(pos, neg)

    goal = [expr("At(C1, JFK)"),
            expr("At(C2, SFO)"),
            expr("At(C3, SFO)"),
            ]

    return AirCargoProblem(cargos, planes, airports, init, goal)


def air_cargo_p3() -> AirCargoProblem:
    cargos = ["C1", "C2", "C3", "C4"]
    planes = ["P1", "P2"]
    airports = ["JFK", "SFO", "ATL", "ORD"]

    pos = [expr("At(C1, SFO)"),
           expr("At(C2, JFK)"),
           expr("At(C3, ATL)"),
           expr("At(C4, ORD)"),

           expr("At(P1, SFO)"),
           expr("At(P2, JFK)"),
           ]

    neg = [expr("At(C1, JFK)"),
           expr("At(C1, ATL)"),
           expr("At(C1, ORD)"),

           expr("At(C2, SFO)"),
           expr("At(C2, ATL)"),
           expr("At(C2, ORD)"),

           expr("At(C3, SFO)"),
           expr("At(C3, JFK)"),
           expr("At(C3, ORD)"),

           expr("At(C4, SFO)"),
           expr("At(C4, JFK)"),
           expr("At(C4, ATL)"),

           expr("At(P1, JFK)"),
           expr("At(P1, ATL)"),
           expr("At(P1, ORD)"),

           expr("At(P1, SFO)"),
           expr("At(P1, ATL)"),
           expr("At(P1, ORD)"),

           # FIXME Testing showing 8 fluents missing. Review missing
           # "in" operators?
           expr("In(C1, P1)"),
           expr("In(C1, P2)"),

           expr("In(C2, P1)"),
           expr("In(C2, P2)"),

           expr("In(C3, P1)"),
           expr("In(C3, P2)"),

           expr("In(C4, P1)"),
           expr("In(C4, P2)"),
           ]

    init = FluentState(pos, neg)

    goal = [expr("At(C1, JFK)"),
            expr("At(C3, JFK)"),
            expr("At(C2, SFO)"),
            expr("At(C4, SFO)"),
            ]

    return AirCargoProblem(cargos, planes, airports, init, goal)
