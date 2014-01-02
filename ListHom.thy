theory ListHom 
imports Main 
begin

(*
  This theory is an attempt to formalize the paper
  "Functional Pearls: The Third Homomorphism Theorem,
  J. Gibbons, 1995".
*)

definition hom' :: "['a list \<Rightarrow> 'b, 'b \<Rightarrow> 'b \<Rightarrow> 'b] \<Rightarrow> bool" 
  where "hom' h b \<longleftrightarrow> (\<forall> xs ys. b (h xs) (h ys) = h (xs @ ys))"

lemma hom'_lunit:
  assumes "hom' h b" 
  shows   "\<forall> x \<in> range h. b (h []) x = x"
  proof
    fix x 
    assume "x \<in> range h"
    then obtain y where * : "x = h y" ..
    then have "b (h []) x = b (h []) (h y)" by simp
    also have "... = h y" using assms by (simp add : hom'_def)
    also have "... = x" using * by simp
    finally show "b (h []) x = x" .
    qed

lemma hom'_runit:
  assumes "hom' h b" 
  shows   "\<forall> x \<in> range h. b x (h []) = x"
  proof 
    fix x 
    assume "x \<in> range h"
    then obtain y where * : "x = h y" ..
    then have "b x (h []) = b (h y) (h [])" by simp
    also have "... = h y" using assms by (simp add : hom'_def)
    also have "... = x" using * by simp
    finally show "b x (h []) = x" .
    qed

(*
should be modelled with universal quantifier like the units:

lemma hom'_assoc: 
  assumes h' : "hom' h b" 
  and     x' : "x = h xs" 
  and     y' : "y = h ys" 
  and     z' : "z = h zs"
  shows   "b (b x y) z = b x (b y z)"
  proof -
    note x' y' h' then
    have "b (b x y) z = b (h (xs @ ys)) z" by (simp only: hom'_def)
    also from z' 
    have "... = b (h (xs @ ys)) (h zs)" by simp
    also from h'
    have "... = h (xs @ ys @ zs)" by (simp add: hom'_def)
    also from h'
    have "... = b (h xs) (h (ys @ zs))" by (simp add: hom'_def)
    also from x' 
    have "... = b x (h (ys @ zs))" by simp
    also note y' z' h' then
    have "... = b x (b y z)" by (simp only: hom'_def)
    finally show ?thesis .
    qed
*)

fun wrap :: "'a \<Rightarrow> 'a list" 
  where "wrap x = [x]"

lemma wrap_inj: 
  shows "inj wrap"
  proof (rule injI)
    fix x y
    assume "wrap x = wrap y"
    thus "x = y" by simp
  qed

(*
 without initial goal refinement:

  lemma wrap_inj: 
    shows "inj wrap"
    proof -
      have "\<And> x y. wrap x = wrap y \<Longrightarrow> x = y"
      proof -
        fix x y
        assume "wrap x = wrap y"
        thus "x = y" by simp
      qed
      thus ?thesis by (rule injI)
    qed
*)

definition hom :: "['a list \<Rightarrow> 'b, 'b \<Rightarrow> 'b \<Rightarrow> 'b, 'a \<Rightarrow> 'b, 'b] \<Rightarrow> bool"
  where "hom h b f e \<longleftrightarrow> (hom' h b) \<and> (h \<circ> wrap = f) \<and> (h [] = e)"

lemma hom_impl_hom': 
  assumes "hom h b f e"
  shows   "hom' h b"
  proof -
    from assms
    show ?thesis
      unfolding hom_def
      by (rule conjE)
    qed

lemma hom_uniq:
  assumes  h' : "hom h b f e"
  and      g' : "hom g b f e"
  shows    "h = g"
  proof 
    fix xs 
    show "h xs = g xs"
    proof (induct xs)
      case Nil
      thus ?case
        using h' and g'
        by (simp add: hom_def)
    next
      case (Cons x xs')
      thus ?case
      proof -
        assume "h xs' = g xs'"
        moreover have "h [x] = g [x]"
        proof - 
          have "f x = f x" by simp
          also have "(h \<circ> wrap) x = (g \<circ> wrap) x"
            using h' and g'
            by (simp only: hom_def)
          thus ?thesis by simp
        qed
        ultimately have "b (h [x]) (h xs') = b (g [x]) (g xs')" by simp
        thus "h (x # xs') = g (x # xs')"  oops
        
lemma hom_impl_map:
  assumes  "hom m (op @) (wrap \<circ> f) e"
  shows    "m = map f"
  proof 
    fix xs
    show "m xs = map f xs"
      proof (induct xs)
        case Nil 
        thus ?case          
        proof -
          have "m [] = m ([] @ [])" 
            by simp 
          also 
          have "... = (m []) @ (m [])"
            oops

theorem fst_hom:
  assumes h' : "hom h b f"
  shows   "\<exists> r. hom r b id \<and> h = r \<circ> map f"
  oops

end