from lark import Lark, Transformer, v_args


@v_args(inline=True)    # Affects the signatures of the methods
class EvalTree(Transformer):
    # from operator import add, sub, mul, truediv as div, neg
    # number = float

    # def __init__(self):
    #     self.vars = {}

    # def assign_var(self, name, value):
    #     self.vars[name] = value
    #     return value

    # def var(self, name):
    #     return self.vars[name]
    pass


coq_parser = Lark(open('jeremy_coq.lark'),
                  parser='lalr',
                  transformer=EvalTree(), debug=True)


def main():
    while True:
        try:
            s = input('> ')
        except EOFError:
            break
        print(coq_parser.parse(s))


def test():
    #     print(coq_parser.parse("""
    # Lemma O_or_S :
    #   forall n : nat,
    #     n = 0 \/ (exists n' : nat,
    #                  n = S n').
    # Proof.
    #   intro n.
    #   destruct n as [ | n'] eqn:H_n.

    #   - left.
    #     reflexivity.

    #   - right.
    #     exists n'.
    #     reflexivity.
    # Qed.
    # """).pretty())
    t = coq_parser.parse("""
    (* week-06_miscellany.v *)
    (* FPP 2019 - YSC3236 2019-2020, Sem1 *)
    (* Olivier Danvy <danvy@yale-nus.edu.sg> *)
    (* Version of 17 Sep 2019 *)

    (* ********** *)

    (*Require Import Arith Bool.*)

    (* ********** *)

    Lemma truism :
    forall P : nat -> Prop,
        (exists n : nat,
            P n) ->
        exists n : nat,
        P n.
    Proof.
    intros P H_P.
    destruct H_P as [n H_Pn].
    exists n.
    exact H_Pn.

    Restart.

    intros P [n H_Pn].
    exists n.
    exact H_Pn.
    Qed.


    (* ********** *)

    (* end of week-06_miscellany.v *)

    """)
    print(t)
    print(t.pretty())


if __name__ == '__main__':
    test()
    # main()
