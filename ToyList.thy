theory ToyList imports Datatype begin

datatype 'a list = Nil                ("[]")
                 | Cons 'a "'a list"  (infixr "#" 65)

primrec app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixr "@" 65) where
"[] @ ys       = ys" |
"(x # xs) @ ys = x # (xs @ ys)"

primrec rev :: "'a list \<Rightarrow> 'a list" where
"rev [] = []" |
"rev (x # xs) = (rev xs) @ (x # [])"

lemma app_Nil [simp]: "xs @ [] = xs"
  apply (induct_tac xs)
  apply auto
  done

lemma app_assoc [simp]: "(xs @ ys) @ zs = xs @ (ys @ zs)"
  apply (induct_tac xs)
  apply auto
  done

lemma rev_app [simp]: "rev (xs @ ys) = (rev ys) @ (rev xs)"
  apply (induct_tac xs)
  apply auto
  done

theorem rev_rev [simp]: "rev (rev xs) = xs"
  apply (induct_tac xs)
  apply auto
  done

end
