theory ListHom 
imports Main 
begin

text
  {*
  This theory is an attempt to formalize the paper
  "Functional Pearls: The Third Homomorphism Theorem,
  J. Gibbons, 1995".
  *}

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
    {
      fix xs ys zs
      assume "xs \<in> range h"
      then obtain xs' where 1 : "xs = h xs'" ..
      assume "ys \<in> range h" 
      then obtain ys' where 2 : "ys = h ys'" ..
      assume "zs \<in> range h" 
      then obtain zs' where 3 : "zs = h zs'" ..
      have "b xs (b ys zs) = b (h xs') (h (ys' @ zs'))"
        using 1 2 3 and assms by (simp only: hom'_def)
      also have "... = h (xs' @ ys' @ zs')" 
        using assms by (simp only: hom'_def)
      also have "... = b (h (xs' @ ys')) (h zs')" 
        using assms by (simp add: hom'_def)
      finally have "b xs (b ys zs) = b (b xs ys) zs" 
        using 1 2 3 and assms by (simp add: hom'_def)
    }
    thus ?thesis by simp
    qed

fun wrap :: "'a \<Rightarrow> 'a list" 
  where "wrap x = [x]"

lemma inj_wrap: 
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
    fix xs show "h xs = g xs"
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

definition uniq_hom ::"['b \<Rightarrow> 'b \<Rightarrow> 'b, 'a \<Rightarrow> 'b, 'b] \<Rightarrow> ('a list \<Rightarrow> 'b)" 
  where "uniq_hom b f e = (SOME h. hom h b f e)"

lemma hom_impl_uniq_hom:
  assumes "hom h b f e"
  shows   "uniq_hom b f e = h"
  proof -
    {
      have "\<And> g. hom g b f e \<Longrightarrow> g = h"
      proof -
        fix g
        assume "hom g b f e"
        with assms 
        show "g = h" by (rule hom_uniq [symmetric])
      qed
    }
    thus ?thesis 
      unfolding uniq_hom_def using assms by blast
  qed
   
lemma uniq_map: 
  shows "uniq_hom (op @) (wrap \<circ> f) [] = map f"  
  proof -
    have "hom' (map f) (op @)"
      unfolding hom'_def by simp
    moreover have "(map f) \<circ> wrap = wrap \<circ> f "
    proof
      fix x 
      have "((map f) \<circ> wrap) x = [f x]" by simp
      also have "... = (wrap \<circ> f) x" by simp
      finally show "((map f) \<circ> wrap) x = (wrap \<circ> f) x" .
    qed
    moreover have "map f [] = []" by simp
    ultimately have "hom (map f) (op @) (wrap \<circ> f) []"
      unfolding hom_def by blast 
    thus ?thesis by (rule hom_impl_uniq_hom)
  qed

(*      
original version:

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
        case (Cons x xs') thus ?case
        proof -
          assume "m xs' = map f xs'"
          moreover have "m [x] = map f [x]"
          proof -
            have "m [x] = (m \<circ> wrap) x" by simp
            also have "... = (wrap \<circ> f) x" 
              using assms by (simp add: hom_def)
            also have "... = map f [x]" by simp
            finally show "m [x] = map f [x]" .
          qed
          ultimately have "(m [x]) @ (m xs') = (map f [x]) @ (map f xs')" by simp
          with hom_impl_hom' [OF assms] 
          show "m (x # xs') = map f (x # xs')" by (simp add: hom'_def)
        qed
      qed
    qed
*)          

theorem fst_hom_v1:
  assumes hom_h : "hom h b f e"
  and     hom_r : "hom r b id e" 
  shows   "h = r \<circ> map f"
  proof 
    fix xs show "h xs = (r \<circ> map f) xs"  
    proof (induct xs)
      case Nil thus ?case
      proof -
        have "h [] = e" 
          using hom_h unfolding hom_def by simp
        also have "... = (r \<circ> map f) []" 
          using hom_r unfolding hom_def by simp
        finally show ?thesis .
      qed
    next
      case (Cons x xs') note ih = Cons thus ?case
      proof -
        {
          have  "h [x] = (r \<circ> map f) [x]"
          proof -
            have "h [x] = (h \<circ> wrap) x" by simp
            also have "... = f x"
              using hom_h unfolding hom_def by simp
            also have "... = (r \<circ> wrap) (f x)"
              using hom_r unfolding hom_def by simp
            finally show ?thesis by simp
          qed
        }
        note single_eq = this
        have "h (x # xs') = b (h [x]) (h xs')" 
          using hom_impl_hom'[OF hom_h] by (simp add: hom'_def)
        also have "... = b ((r \<circ> map f) [x]) ((r \<circ> map f) xs')" 
          using ih and single_eq by simp               
        also have "... = r (map f [x] @ map f xs')"
          using hom_impl_hom'[OF hom_r] by (simp add: hom'_def)
        finally show ?thesis by simp
      qed
    qed
  qed

theorem fst_hom_v2:
  assumes "\<exists> h. hom h b f e"
  and     "\<exists> r. hom r b id e"
  shows   "uniq_hom b f e = uniq_hom b id e \<circ> map f"
  proof -
    from assms(1) obtain h where hom_h: "hom h b f e" ..
    from assms(2) obtain r where hom_r: "hom r b id e" ..
    have "h = r \<circ> map f" by (rule fst_hom_v1[OF hom_h hom_r])
      thus ?thesis
        using hom_impl_uniq_hom[OF hom_h] and hom_impl_uniq_hom[OF hom_r] by simp  
    qed

primrec foldr' :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a"
  where "foldr' b e []       = e"
  |     "foldr' b e (x # xs) = b x (foldr' b e xs)" 
(* this function had been introduced for its type,
   which differs from that of foldr *)

lemma uniq_foldr':
  assumes "\<exists> h. hom h b f e"
  shows   "uniq_hom b id e = foldr' b e"
  proof -
    from assms obtain h where hom_h: "hom h b f e" ..
    have "hom (foldr' b e) b id e"
      unfolding hom_def 
    proof
      have "hom' (foldr' b e) b"
        oops

end