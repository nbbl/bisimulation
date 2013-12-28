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

lemma hom'_b_lunit:
  assumes h' : "hom' h b" 
  and     x' : "x = h xs" 
  and     e' : "e = h []"
  shows   "b e x = x"
  proof - 
    have "b e x = b (h []) x" 
      using e'  by simp
    also have "... = b (h []) (h xs)" 
      using x' by simp
    also have "... = h ([] @ xs)" 
      using h' by (simp only: hom'_def)
    also have "... = h xs" 
      by simp
    also have "... = x" 
      using x' by simp
    finally show ?thesis .
    qed


lemma hom'_b_runit:
  assumes h' : "hom' h b" 
  and     x' : "x = h xs" 
  and     e' : "e = h []"
  shows   "b x e = x"
  proof - 
    have "b x e = b x (h [])" 
      using e' by simp
    also have "... = b (h xs) (h [])" 
      using x' by simp
    also have "... = h (xs @ [])" 
      using h' by (simp only: hom'_def)
    also have "... = h xs" 
      by simp
    also have "... = x" 
      using x' by simp
    finally show ?thesis .
    qed

lemma hom'_b_assoc:
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

definition hom :: "['a list \<Rightarrow> 'b, 'b \<Rightarrow> 'b \<Rightarrow> 'b, 'a \<Rightarrow> 'b] \<Rightarrow> bool"
  where "hom h b f \<longleftrightarrow> (hom' h b) \<and> (h \<circ> wrap = f)"

lemma hom_uniq:
  assumes  h' : "hom h b f"
  and      g' : "hom g b f"
  shows    "h = g"
  proof -
    from h'
    have "h \<circ> wrap = f" 
      by (simp only: hom_def)
    also from g'
    have "... = g \<circ> wrap" 
      by (simp add: hom_def)
    finally 
    have "h \<circ> wrap = g \<circ> wrap" .
    then have "h = g" oops
(* needs proof of left cancellation of inj funs *)
     
lemma hom_impl_map:
  assumes  "hom m (op @) (wrap \<circ> f)"
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
            proof - (* this might be a candidate for an accessor *)
              from assms
              have "hom' m (op @)" 
                unfolding hom_def
                by (rule conjE)
              thus ?thesis
                unfolding hom'_def
                by simp
              qed 
              thus ?thesis 
                by simp
          qed

theorem fst_hom:
  assumes h' : "hom h b f"
  shows   "\<exists> r. hom r b id \<and> h = r \<circ> map f"
          
end