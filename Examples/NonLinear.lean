import IIT

mutual

iit A : Type where
| a0 : A
| a1 : A

iit B : (a a' : A) → Type where
| foo : (a : A) → B a a

end

noncomputable def Con_total' : B.tot  := by
  totalityOuter 1 [A, B] [A.a0, A.a1] [B.foo]
  apply A.a0.m
  apply A.a0.r
  apply A.a1.m
  apply A.a1.r
  have a.m = a'.m := by
    cases a.r <;> cases a'.r <;> rfl
  cases this
  apply B.foo.m
  have a.m = a'.m := by
    cases a.r <;> cases a'.r <;> rfl
  cases this
  apply B.foo.r
  assumption
  