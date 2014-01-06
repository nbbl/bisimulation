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

lemma hom'_l_id:
  assumes "hom' h b" 
  shows   "\<forall> xs \<in> range h. b (h []) xs = xs"
  proof
    fix xs 
    assume "xs \<in> range h"
    then obtain xs' where * : "xs = h xs'" ..
    then have "b (h []) xs = b (h []) (h xs')" by simp
    also have "... = h xs'" using assms by (simp add : hom'_def)
    also have "... = xs" using * by simp
    finally show "b (h []) xs = xs" .
  qed

lemma hom'_r_id:
  assumes "hom' h b" 
  shows   "\<forall> xs \<in> range h. b xs (h []) = xs"
  proof 
    fix xs 
    assume "xs \<in> range h"
    then obtain xs' where * : "xs = h xs'" ..
    then have "b xs (h []) = b (h xs') (h [])" by simp
    also have "... = h xs'" using assms by (simp add : hom'_def)
    also have "... = xs" using * by simp
    finally show "b xs (h []) = xs" .
  qed

lemma hom'_assoc:
  assumes "hom' h b"
  shows   "\<forall> xs \<in> range h. \<forall> ys \<in> range h. \<forall> zs \<in> range h. 
           b xs (b ys zs) = b (b xs ys) zs"
  proof - 
    fix xs ys zs
    assume "xs \<in> range h" 
    then obtain xs' where 1 : "xs = h xs'" ..
    assume "ys \<in> range h" 
    then obtain ys' where 2 : "ys = h ys'" ..
    assume "zs \<in> range h" 
    then obtain zs' where 3 : "zs = h zs'" ..
    from 1 2 3 and assms
    have "b xs (b ys zs) = b (h xs') (h (ys' @ zs'))" by (simp only: hom'_def)
    also have  "... = h (xs' @ ys' @ zs')" oops

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
      unfolding hom_def by (rule conjE)
  qed

lemma hom_uniq:
  assumes  hom_h : "hom h b f e"
  and      hom_g : "hom g b f e"
  shows    "h = g"
  proof 
    fix xs 
    show "h xs = g xs"
    proof (induct xs)
      case Nil thus ?case
        using hom_h and hom_g by (simp add: hom_def)
    next
      case (Cons x xs') thus ?case
      proof -
        assume "h xs' = g xs'"
        moreover have "h [x] = g [x]"
        proof - 
          have "f x = f x" by simp
          also have "(h \<circ> wrap) x = (g \<circ> wrap) x"
            using hom_h and hom_g by (simp only: hom_def)
          thus ?thesis by simp
        qed
        ultimately have "b (h [x]) (h xs') = b (g [x]) (g xs')" by simp
        with hom_impl_hom' [OF hom_h] and hom_impl_hom' [OF hom_g]
        show "h (x # xs') = g (x # xs')" by (simp add: hom'_def)
      qed
    qed
  qed
        
lemma hom_app_eq_map:
  assumes  "hom m (op @) (wrap \<circ> f) []"
  shows    "m = map f"
  proof 
    fix xs show "m xs = map f xs"
      proof (induct xs)
        case Nil thus ?case          
        proof -
          from assms have "m [] = []" by (simp only: hom_def)
          also have "... = map f []" by simp 
          finally show "m [] = map f []" .
        qed
      next
        case Cons thus ?case
        proof -
          oops

theorem fst_hom:
  assumes "hom h b f e"
  shows   "\<exists> r. (hom r b id e) \<and> (h = r \<circ> map f)"
  oops

end