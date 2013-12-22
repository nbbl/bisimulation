theory ListHom 
imports Main 
begin

{*
  This theory is an attempt to formalize the paper
  "Functional Pearls: The Third Homomorphism Theorem,
  J. Gibbons, 1995".
*}

definition hom :: "['a list \<Rightarrow> 'b, 'b \<Rightarrow> 'b \<Rightarrow> 'b] \<Rightarrow> bool" 
  where "hom h f = (\<forall> xs ys. f (h xs) (h ys) = h (xs @ ys))"

lemma hom_f_lunit:
  assumes h' : "hom h f" 
  and     x' : "x = h xs" 
  and     e' : "e = h []"
  shows   "f e x = x"
  proof - 
    from e'
    have "f e x = f (h []) x" by simp
    also from x'
    have "... = f (h []) (h xs)" by simp
    also from h' 
    have "... = h ([] @ xs)" by (simp only: hom_def)
    also have "... = h xs" by simp
    also from x'
    have "... = x" by simp
    finally show ?thesis .
    qed

lemma hom_f_runit:
  assumes h' : "hom h f" 
  and     x' : "x = h xs" 
  and     e' : "e = h []"
  shows   "f x e = x"
  proof - 
    from e'
    have "f x e = f x (h [])" by simp
    also from x'
    have "... = f (h xs) (h [])" by simp
    also from h' 
    have "... = h (xs @ [])" by (simp only: hom_def)
    also have "... = h xs" by simp
    also from x'
    have "... = x" by simp
    finally show ?thesis .
    qed

lemma hom_f_assoc:
  assumes h' : "hom h f" 
  and     x' : "x = h xs" 
  and     y' : "y = h ys" 
  and     z' : "z = h zs"
  shows   "f (f x y) z = f x (f y z)"
  proof -
    note x' y' h' then
    have "f (f x y) z = f (h (xs @ ys)) z" by (simp only: hom_def)
    also from z' 
    have "... = f (h (xs @ ys)) (h zs)" by simp
    also from h'
    have "... = h (xs @ ys @ zs)" by (simp add: hom_def)
    also from h'
    have "... = f (h xs) (h (ys @ zs))" by (simp add: hom_def)
    also from x' 
    have "... = f x (h (ys @ zs))" by simp
    also note y' z' h' then
    have "... = f x (f y z)" by (simp only: hom_def)
    finally show ?thesis .
    qed
          
end