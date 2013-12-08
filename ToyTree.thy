theory ToyTree 
imports Datatype 
begin

datatype 'a tree = Leaf 
                 | Node "'a tree" 'a "'a tree"

primrec mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Leaf = Leaf" |
"mirror (Node lt n rt) = Node (mirror rt) n (mirror lt)"

lemma mirror_mirror: "mirror (mirror t) = t"
  apply (induct_tac t)
  apply auto
  done

end
