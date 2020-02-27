from lark import Lark, Transformer, v_args


grammar = open('jeremy-coq.lark')


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


coq_parser = Lark(grammar, parser='lalr', transformer=EvalTree(), debug=True)


def main():
    while True:
        try:
            s = input('> ')
        except EOFError:
            break
        print(coq_parser.parse(s))


def test():
    print(coq_parser.parse("""
    Lemma truism : forall P : nat -> Prop, (exists n : nat, P n) -> exists n : nat, P n.
    Proof.
    intros P H_P H_P.
    destruct H_P as [n H_P].
    exists n.
    exact H_Pn.
    rewrite -> (first_formal_proof).
    Restart.
    intros P [n H_Pn].
    exists n.
    exact H_Pn.
    Qed.""").pretty())
    # print(coq_parser.parse("""
    # Lemma truism : forall P : nat -> Prop, (exists n : nat, P n) -> exists n : nat, P n.
    # Proof.
    # intros.
    # Qed.""").pretty())


if __name__ == '__main__':
    test()
    # main()
