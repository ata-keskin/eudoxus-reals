theory Almost_Homomorphism
imports Main
begin

definition bounded :: "('a \<Rightarrow> int) \<Rightarrow> bool" where
  "bounded f \<longleftrightarrow> bdd_above ((\<lambda>z. \<bar>f z\<bar>) ` UNIV)"

lemma boundedI:
  assumes "\<And>z. \<bar>f z\<bar> \<le> C"
  shows "bounded f"
  unfolding bounded_def by (rule bdd_aboveI2, force intro: assms)

lemma boundedE:
  assumes "bounded f" "\<exists>C. (\<forall>z. \<bar>f z\<bar> \<le> C) \<and> 0 \<le> C \<Longrightarrow> P"
  shows P
  using assms[unfolded bounded_def bdd_above_def] by fastforce

lemma boundedE2:
  assumes "bounded f" "\<exists>C. (\<forall>z. \<bar>f z\<bar> < C) \<and> 0 < C \<Longrightarrow> P"
  shows P
  using assms[unfolded bounded_def bdd_above_def] by (meson assms(1) boundedE gt_ex order.strict_trans1)

lemma bounded_alt_def:
  "bounded f \<longleftrightarrow> (\<exists>C. \<forall>z. \<bar>f z\<bar> \<le> C)" using boundedI boundedE by meson

lemma bounded_iff_finite_range: "bounded f \<longleftrightarrow> finite (range f)"
proof
  assume "bounded f"
  then obtain C where bound: "\<bar>z\<bar> \<le> C" if "z \<in> range f" for z  by (blast elim: boundedE)
  from abs_le_D1[OF bound] abs_le_D2[OF bound] have "range f \<subseteq> {z. z \<le> C \<and> -z \<le> C}" by blast
  also have "... = {(-C)..C}" by force
  finally show "finite (range f)" using finite_subset finite_atLeastAtMost_int by blast
next
  assume asm: "finite (range f)"
  let ?C = "max (abs (Sup (range f))) (abs (Inf (range f)))"
  show "bounded f"
  proof (rule boundedI)
    fix z
    have f_z: "f z \<in> range f" by simp
    from cInf_lower[OF f_z bdd_below_finite[OF asm]] cSup_upper[OF f_z bdd_above_finite[OF asm]]
    show "\<bar>f z\<bar> \<le> ?C" by linarith
  qed
qed

lemma bounded_constant:
  shows "bounded (\<lambda>_. c)"
  by (rule boundedI[of _ "\<bar>c\<bar>"], blast)

lemma bounded_add:
  assumes "bounded f" "bounded g"
  shows "bounded (\<lambda>z. f z + g z)"
proof -
  from assms[THEN boundedE] obtain C_f C_g where "\<bar>f z\<bar> \<le> C_f" "\<bar>g z\<bar> \<le> C_g" for z by meson
  then have "\<bar>f z + g z\<bar> \<le> C_f + C_g" for z by (meson abs_triangle_ineq add_mono dual_order.trans)
  thus ?thesis by (blast intro: boundedI)
qed

lemma bounded_mult:
  assumes "bounded f" "bounded g"
  shows "bounded (\<lambda>z. f z * g z)"
proof -
  from assms obtain C where b: "\<bar>f z\<bar> \<le> C" and C_nonneg: "0 \<le> C" for z by (blast elim: boundedE)
  from assms obtain C' where b': "\<bar>g z\<bar> \<le> C'" for z by (blast elim: boundedE)
  show ?thesis by (simp only: boundedI[of "\<lambda>z. f z * g z" "C * C'"] mult_mono[OF b b' C_nonneg abs_ge_zero, unfolded abs_mult[symmetric]])
qed

lemma bounded_mult_c:
  assumes "bounded f"
  shows "bounded (\<lambda>z. c * f z)"
  by (rule bounded_mult[OF bounded_constant[of c] assms])

lemma bounded_uminus:
  assumes "bounded f"
  shows "bounded (\<lambda>z. - f z)"
  using bounded_mult_c[OF assms, of "- 1"] by simp

lemma bounded_comp:
  assumes "bounded f"
  shows "bounded (f o g)" and "bounded (g o f)"
proof (goal_cases)
  case 1
  show ?case using assms by (metis boundedI boundedE comp_def)
next
  case 2
  have "range (g o f) = g ` range f" by fastforce
  thus ?case using assms[unfolded bounded_iff_finite_range] by (fastforce simp: bounded_iff_finite_range)
qed

definition almost_hom :: "(int \<Rightarrow> int) \<Rightarrow> bool" where
  "almost_hom f \<longleftrightarrow> bounded (\<lambda>(m, n). f (m + n) - (f m + f n))"

lemma almost_hom_add:
  assumes "almost_hom f" "almost_hom g"
  shows "almost_hom (\<lambda>z. f z + g z)"
proof -
  from assms(1)[unfolded almost_hom_def]
  obtain C where phi_bound: "\<bar>f (m + n) - (f m + f n)\<bar> \<le> C" for m n by (fastforce elim: boundedE)
  from assms(2)[unfolded almost_hom_def]
  obtain C' where phi'_bound: "\<bar>g (m + n) - (g m + g n)\<bar> \<le> C'" for m n by (fastforce elim: boundedE)

  from phi_bound phi'_bound have "\<bar>f (m + n) - (f m + f n)\<bar> + \<bar>g (m + n) - (g m + g n)\<bar> \<le> C + C'" for m n 
    using add_mono_thms_linordered_semiring(1) by blast
  moreover have "\<bar>(\<lambda>z. f z + g z) (m + n) - ((\<lambda>z. f z + g z) m + (\<lambda>z. f z + g z) n)\<bar> \<le> \<bar>f (m + n) - (f m + f n)\<bar> + \<bar>g (m + n) - (g m + g n)\<bar>" for m n by linarith
  ultimately have "\<bar>(\<lambda>z. f z + g z) (m + n) - ((\<lambda>z. f z + g z) m + (\<lambda>z. f z + g z) n)\<bar> \<le> C + C'" for m n using order.trans by blast
  thus "almost_hom (\<lambda>z. f z + g z)" unfolding almost_hom_def by (fast intro: boundedI)
qed

lemma almost_hom_symmetric_bound:
  assumes "almost_hom f"
  obtains C where "\<forall>p q. \<bar>p * f q - q * f p\<bar> \<le> (\<bar>p\<bar> + \<bar>q\<bar> + 2) * C" "0 \<le> C"
proof-
  from assms[unfolded almost_hom_def] obtain C where f_bound: "\<bar>f (m + n) - (f m + f n)\<bar> \<le> C" and C_nonneg: "0 \<le> C" for m n by (fastforce elim: boundedE)
  
  have ineq: "\<bar>f (p * q) - p * f q\<bar> \<le> (\<bar>p\<bar> + 1) * C" for p q
  proof (induction p rule: int_induct[where ?k=0])
    case base
    then show ?case using f_bound[of 0 0] by force
  next
    case (step1 p)
    from f_bound[of "p * q" q] have "\<bar>f ((p + 1) * q) - f (p * q) - f q\<bar> \<le> C" by (auto simp: distrib_left mult.commute)
    with step1(2) have "\<bar>f ((p + 1) * q) - f q - p * f q\<bar> \<le> C + (\<bar>p\<bar> + 1) * C" by fastforce
    with step1(1) show ?case by (auto simp add: distrib_left mult.commute)
  next
    case (step2 p)
    from f_bound[of "p * q - q" "q"] have "\<bar>f ((p - 1) * q) + f q - f (p * q)\<bar> \<le> C" by (auto simp: mult.commute right_diff_distrib')
    with step2(2) have "\<bar>f ((p - 1) * q) + f q - p * f q\<bar> \<le> C + (\<bar>p\<bar> + 1) * C" by force
    with step2(1) have "\<bar>f ((p - 1) * q) - (p - 1) * f q\<bar> \<le> C + (\<bar>p - 1\<bar>) * C" by (auto simp: mult.commute right_diff_distrib')
    thus ?case by (auto simp add: distrib_left mult.commute)
  qed

  have "\<bar>p * f q - q * f p\<bar> \<le> (\<bar>p\<bar> + \<bar>q\<bar> + 2) * C" for p q
  proof -
    have "\<bar>p * f q - q * f p\<bar> \<le> \<bar>f (p * q) - p * f q\<bar> + \<bar>f (q * p) - q * f p\<bar>" by (fastforce simp: mult.commute)
    also from ineq[of p q] ineq[of q p] have "... \<le> (\<bar>p\<bar> + 1) * C + (\<bar>q\<bar> + 1) * C" by fastforce
    also have "... = (\<bar>p\<bar> + \<bar>q\<bar> + 2) * C" by algebra
    finally show ?thesis .
  qed
  thus ?thesis using that C_nonneg by blast
qed

lemma almost_hom_linear_bound:
  assumes "almost_hom f"
  obtains A B where "\<forall>n. \<bar>f n\<bar> \<le> A * \<bar>n\<bar> + B" "0 \<le> A" "0 \<le> B"
proof-
  from almost_hom_symmetric_bound[OF assms] 
  obtain C where bound: "\<bar>p * f q - q * f p\<bar> \<le> (\<bar>p\<bar> + \<bar>q\<bar> + 2) * C" "0 \<le> C" for p q by blast
 
  have "\<bar>f p\<bar> \<le> (C + \<bar>f 1\<bar>) * \<bar>p\<bar> + 3 * C" for p
  proof -
    from bound(1)[of _ 1] have "\<bar>p * f 1 - f p\<bar> \<le> (\<bar>p\<bar> + 3) * C" by (simp add: add.commute)
    hence "\<bar>f p - p * f 1\<bar> \<le> (\<bar>p\<bar> + 3) * C" by (subst abs_minus[of "f p - p * f 1", symmetric], simp)
    hence "\<bar>f p\<bar> \<le> (\<bar>p\<bar> + 3) * C + \<bar>p * f 1\<bar>" using dual_order.trans abs_triangle_ineq2 diff_le_eq by fast
    hence "\<bar>f p\<bar> \<le> \<bar>p\<bar> * C + 3 * C + \<bar>p\<bar> * \<bar>f 1\<bar>" by (simp add: abs_mult int_distrib(2) mult.commute)
    hence "\<bar>f p\<bar> \<le> \<bar>p\<bar> * (C + \<bar>f 1\<bar>) + 3 * C" by (simp add: ring_class.ring_distribs(1))
    thus ?thesis using mult.commute by metis
  qed
  thus ?thesis using that bound(2) by fastforce
qed

(* OLD VERSION:

lemma almost_hom_linear_bound:
  assumes "almost_hom f"
  obtains A B where "\<forall>n. \<bar>f n\<bar> \<le> A * \<bar>n\<bar> + B" "0 \<le> A" "0 \<le> B"
proof-
  from assms[unfolded almost_hom_def] obtain C where f_bound: "\<bar>f (m + n) - (f m + f n)\<bar> \<le> C" for m n by (fastforce elim: boundedE)
  then have C_nonneg: "0 \<le> C" by fastforce
  have "\<bar>f n\<bar> \<le> (C + max \<bar>f 1\<bar> \<bar>f (-1)\<bar>) * \<bar>n\<bar> + C" for n
  proof (induct n rule: int_induct[where ?k=0])
    case base
    then show ?case using f_bound[of 0 0] by force
  next
    case (step1 i)
    from f_bound[of i 1] have "\<bar>f (i + 1)\<bar> \<le> \<bar>f i\<bar> + \<bar>f 1\<bar> + C" by linarith
    with step1 have "\<bar>f (i + 1)\<bar> \<le> (C + max \<bar>f 1\<bar> \<bar>f (- 1)\<bar>) * \<bar>i\<bar> + C + \<bar>f 1\<bar> + C" by linarith
    also have "... \<le> (C + max \<bar>f 1\<bar> \<bar>f (- 1)\<bar>) * \<bar>i\<bar> + (C + max \<bar>f 1\<bar> \<bar>f (- 1)\<bar>) + C" by fastforce
    also have "... = (C + max \<bar>f 1\<bar> \<bar>f (- 1)\<bar>) * (\<bar>i\<bar> + 1) + C" by algebra
    also from step1(1) have "... = (C + max \<bar>f 1\<bar> \<bar>f (- 1)\<bar>) * \<bar>i + 1\<bar> + C" by force
    finally show ?case by blast
  next
    case (step2 i)
    from f_bound[of i "-1"] have "\<bar>f (i - 1)\<bar> \<le> \<bar>f i\<bar> + \<bar>f (- 1)\<bar> + C" by fastforce
    with step2 have "\<bar>f (i - 1)\<bar> \<le> (C + max \<bar>f 1\<bar> \<bar>f (- 1)\<bar>) * \<bar>i\<bar> + C + \<bar>f (-1)\<bar> + C" by linarith
    also have "... \<le> (C + max \<bar>f 1\<bar> \<bar>f (- 1)\<bar>) * \<bar>i\<bar> + (C + max \<bar>f 1\<bar> \<bar>f (- 1)\<bar>) + C" by fastforce
    also have "... = (C + max \<bar>f 1\<bar> \<bar>f (- 1)\<bar>) * (\<bar>i\<bar> + 1) + C" by algebra
    also from step2(1) have "... = (C + max \<bar>f 1\<bar> \<bar>f (- 1)\<bar>) * \<bar>i - 1\<bar> + C" by force 
    finally show ?case by blast
  qed
  with that C_nonneg show ?thesis by fastforce
qed

*)


lemma almost_hom_comp:
  assumes "almost_hom f" "almost_hom g"
  shows "almost_hom (f o g)"
proof-
  from assms(1)[unfolded almost_hom_def]
  obtain C where f_bound: "\<bar>f (m + n) - (f m + f n)\<bar> \<le> C" for m n by (fastforce elim: boundedE)
  from assms(2)[unfolded almost_hom_def]
  obtain C' where g_bound: "\<bar>g (m + n) - (g m + g n)\<bar> \<le> C'" for m n by (fastforce elim: boundedE)
  from almost_hom_linear_bound[OF assms(1)] 
  obtain A B where f_linear_bound: "\<bar>f n\<bar> \<le> A * \<bar>n\<bar> + B" "0 \<le> A" "0 \<le> B" for n by blast

  show "almost_hom (f o g)" unfolding comp_def almost_hom_def
  proof (rule boundedI, clarsimp)
    fix m n
    have "\<bar>f (g (m + n)) - (f (g m) + f (g n))\<bar> \<le> (\<bar>f (g (m + n)) - f (g m + g n)\<bar> + \<bar>f (g m + g n) - (f (g m) + f (g n))\<bar> :: int)" by linarith
    also have "... \<le> \<bar>f (g (m + n)) - f (g m + g n)\<bar> + C" using f_bound[of "g m" "g n"] by auto
    also have "... \<le> \<bar>f (g (m + n)) - f (g m + g n) - f(g (m + n) - (g m + g n))\<bar> + \<bar>f (g (m + n) - (g m + g n))\<bar> + C" by fastforce
    also from f_bound[of "g (m + n) - (g m + g n)" "(g m + g n)"] have "... \<le> \<bar>f (g (m + n) - (g m + g n))\<bar> + 2 * C" by fastforce
    also from f_linear_bound(1)[of "g (m + n) - (g m + g n)"] have "... \<le> A * \<bar>g (m + n) - (g m + g n)\<bar> + B + 2 * C" by linarith
    also from mult_left_mono[OF g_bound[of m n], OF f_linear_bound(2)]
    have "... \<le> A * C' + B + 2 * C" by presburger
    finally show "\<bar>f (g (m + n)) - (f (g m) + f (g n))\<bar> \<le> A * C' + B + 2 * C" by blast
  qed
qed

lemma almost_hom_scale: "almost_hom ((*) a)" unfolding almost_hom_def by (auto simp: distrib_left intro: boundedI)

lemma almost_hom_zero: "almost_hom (\<lambda>_. 0)" using almost_hom_scale[of 0] by (simp add: lambda_zero)

lemma almost_hom_one: "almost_hom id" by (rule back_subst[of almost_hom, OF almost_hom_scale[of 1]], auto)

lemma almost_hom_uminus: "almost_hom uminus" by (rule back_subst[of almost_hom, OF almost_hom_scale[of "-1"]], auto)

lemma almost_hom_uminus_comp: 
  assumes "almost_hom f"
  shows "almost_hom (\<lambda>z. - f z)"
  by (rule almost_hom_comp[OF almost_hom_uminus assms, unfolded comp_def])

lemma almost_hom_comp_commute:
  assumes "almost_hom f" "almost_hom g"
  shows "bounded (\<lambda>z. (f o g) z - (g o f) z)"
proof -
  from almost_hom_symmetric_bound[OF assms(1)]
  obtain C where bound: "\<bar>z * f (g z) - (g z) * (f z)\<bar> \<le> (\<bar>z\<bar> + \<bar>g z\<bar> + 2) * C" "0 \<le> C" for z by metis
  from almost_hom_symmetric_bound[OF assms(2)]
  obtain C' where bound': "\<bar>(f z) * (g z) - z * g (f z)\<bar> \<le> (\<bar>f z\<bar> + \<bar>z\<bar> + 2) * C'" "0 \<le> C'" for z by metis

  from almost_hom_linear_bound[OF assms(1)]
  obtain A B where f_lbound: "\<bar>f z\<bar> \<le> A * \<bar>z\<bar> + B" "0 \<le> A" "0 \<le> B" for z by blast
  from almost_hom_linear_bound[OF assms(2)]
  obtain A' B' where g_lbound: "\<bar>g z\<bar> \<le> A' * \<bar>z\<bar> + B'" "0 \<le> A'" "0 \<le> B'" for z by blast

  have combined_bound: "\<bar>z * f (g z) - z * g (f z)\<bar> \<le> (\<bar>z\<bar> + \<bar>g z\<bar> + 2) * C + (\<bar>f z\<bar> + \<bar>z\<bar> + 2) * C'" for z 
    by (rule order.trans[OF _ add_mono[OF bound(1)[of z] bound'(1)[of z, unfolded mult.commute[of "f z" "g z"]]]], fastforce)

  show ?thesis
  proof (rule boundedI, clarsimp simp add: comp_def)
    fix z
    define D E where D_def: "D = (C + C' + A' * C + A * C')" and E_def: "E = (2 + B') * C + (2 + B) * C'"
    from g_lbound(3) bound(2) f_lbound(3) bound'(2) have E_nonneg: "0 \<le> E" unfolding E_def by simp
    from g_lbound(2) bound(2) f_lbound(2) bound'(2) have D_nonneg: "0 \<le> D" unfolding D_def by simp

    have "(\<bar>z\<bar> + \<bar>g z\<bar> + 2) * C + (\<bar>f z\<bar> + \<bar>z\<bar> + 2) * C' = \<bar>z\<bar> * (C + C') + \<bar>g z\<bar> * C + \<bar>f z\<bar> * C' + 2 * C + 2 * C'" by algebra
    from combined_bound[of z, unfolded this right_diff_distrib[symmetric] abs_mult]
    have "\<bar>z\<bar> * \<bar>f (g z) - g (f z)\<bar> \<le> \<bar>z\<bar> * (C + C') + \<bar>g z\<bar> * C + \<bar>f z\<bar> * C' + 2 * C + 2 * C'" by blast
    also from mult_right_mono[OF g_lbound(1)[of z] bound(2)] 
    have "... \<le> \<bar>z\<bar> * (C + C') + (A' * \<bar>z\<bar> + B') * C + \<bar>f z\<bar> * C' + 2 * C + 2 * C'" by presburger
    also from mult_right_mono[OF f_lbound(1)[of z] bound'(2)] 
    have "... \<le> \<bar>z\<bar> * (C + C') + (A' * \<bar>z\<bar> + B') * C + (A * \<bar>z\<bar> + B) * C' + 2 * C + 2 * C'" by presburger
    also have "... = \<bar>z\<bar> * (C + C' + A' * C + A * C') + (2 + B') * C + (2 + B) * C'" by algebra
    finally have intermediate_step: "\<bar>z\<bar> * \<bar>f (g z) - g (f z)\<bar> \<le> \<bar>z\<bar> * D + E" unfolding D_def E_def by presburger
    show "\<bar>f (g z) - g (f z)\<bar> \<le> D + E + \<bar>f (g 0) - g (f 0)\<bar>"
    proof (cases "z = 0")
      case True
      then show ?thesis using D_nonneg E_nonneg by fastforce
    next
      case False
      from intermediate_step mult_right_mono[OF Ints_nonzero_abs_ge1[OF _ False, unfolded Ints_def] E_nonneg] distrib_left[symmetric, of "\<bar>z\<bar>" D E]
      have "\<bar>z\<bar> * \<bar>f (g z) - g (f z)\<bar> \<le> \<bar>z\<bar> * (D + E)" by simp
      with False have "\<bar>f (g z) - g (f z)\<bar> \<le> D + E" by simp
      thus ?thesis by linarith
    qed
  qed
qed

lemma int_set_infiniteI:
  assumes "\<forall>C\<ge>0. \<exists>N\<ge>C. N \<in> (A :: int set)" 
  shows "infinite A"
  by (meson assms abs_ge_zero abs_le_iff gt_ex le_cSup_finite linorder_not_less order_less_le_trans)

lemma int_set_infiniteD:
  assumes "infinite (A :: int set)" 
  shows "\<forall>C\<ge>0. \<exists>z\<in>A. C \<le> \<bar>z\<bar>"
proof (rule ccontr, clarsimp, goal_cases)
  case (1 C)
  let ?f = "\<lambda>z. (if z \<in> A then z else (0::int))"
  from 1(2) have bounded: "\<forall>z\<in>A. \<bar>?f z\<bar> \<le> C" by fastforce
  moreover from 1(1) have "\<forall>z\<in>UNIV - A. \<bar>?f z\<bar> \<le> C" by fastforce
  ultimately have "bounded ?f" by (blast intro: boundedI)
  with assms show False using bounded_iff_finite_range by force
qed

lemma almost_hom_anti_symmetric: 
  assumes "\<forall>z. z < 0 \<longrightarrow> f z = -f (-z)" "\<exists>C. \<forall>m \<ge> 0. \<forall>n \<ge> 0. \<bar>f (m + n) - (f m + f n)\<bar> \<le> C"
  shows "almost_hom f"
proof (subst almost_hom_def)
  from assms(2) obtain C where C_bound: "\<bar>f (m + n) - (f m + f n)\<bar> \<le> C" if "m \<ge> 0" "n \<ge> 0" for m n using that by fast
  show "bounded (\<lambda>(m, n). f (m + n) - (f m + f n))"
  proof (rule boundedI, clarify)
    fix m n
    show "\<bar>f (m + n) - (f m + f n)\<bar> \<le> C"
    proof (cases "m \<ge> 0")
      case mp: True
      show ?thesis
      proof (cases "n \<ge> 0")
        case np: True
        with mp C_bound show ?thesis by fast
      next
        case False
        hence nn: "n < 0" by fastforce
        hence nn_pos: "-n \<ge> 0" by fastforce
        from assms(1) nn have f_n: "f n = - f (- n)" by blast
        show ?thesis
        proof (cases "m + n \<ge> 0")
          case True
          from f_n have "\<bar>f (m + n) - (f m + f n)\<bar> = \<bar>f (m + n + -n) - (f (m + n) + f (-n))\<bar>" by auto
          with C_bound[OF True nn_pos] show ?thesis by argo
        next
          case False
          hence m_n_pos: "- (m + n) \<ge> 0" by fastforce
          from False assms(1) have "f (m + n) = - f (- (m + n))" by force
          with f_n have "\<bar>f (m + n) - (f m + f n)\<bar> = \<bar>f (- (m + n) + m) - (f (- (m + n)) + f m)\<bar>" by force
          with C_bound[OF m_n_pos mp] show ?thesis by argo
        qed
      qed
    next
      case False
      hence mn: "m < 0" by fastforce
      hence mn_pos: "-m \<ge> 0" by fastforce
      from assms(1) mn have f_m: "f m = - f (- m)" by blast
      show ?thesis
      proof (cases "n \<ge> 0")
        case np: True
        show ?thesis
        proof (cases "m + n \<ge> 0")
          case True
          from f_m have "\<bar>f (m + n) - (f m + f n)\<bar> = \<bar>f (m + n + -m) - (f (m + n) + f (-m))\<bar>" by auto
          with C_bound[OF True mn_pos] show ?thesis by argo
        next
          case False
          hence m_n_pos: "- (m + n) \<ge> 0" by fastforce
          from False assms(1) have "f (m + n) = - f (- (m + n))" by force
          with f_m have "\<bar>f (m + n) - (f m + f n)\<bar> = \<bar>f (- (m + n) + n) - (f (- (m + n)) + f n)\<bar>" by force
          with C_bound[OF m_n_pos np] show ?thesis by argo
        qed
      next
        case False
        hence nn: "n < 0" by fastforce
        hence nn_pos: "-n \<ge> 0" by fastforce
        from assms(1) nn have f_n: "f n = - f (- n)" by blast
        from assms(1) mn nn
        have "f (m + n) = - f (- m + - n)" by fastforce+
        with f_m f_n have "\<bar>f (m + n) - (f m + f n)\<bar> = \<bar>- f (- m + -n) - (- f (-m) + - f(- n))\<bar>" by argo
        also have "... = \<bar>f (-m + -n) - (f (-m) + f(-n))\<bar>" by linarith
        finally show ?thesis using C_bound[OF mn_pos nn_pos] by presburger
      qed
    qed
  qed
qed

lemma almost_hom_bounded_comp_right_abs:
  assumes "almost_hom f" "bounded (f o abs)"
  shows "bounded f"
proof -
  from assms(2)[unfolded comp_def]
  obtain B where "\<forall>z. \<bar>f \<bar>z\<bar>\<bar> \<le> B" and B_nonneg: "0 \<le> B" by (blast elim: boundedE)
  then have B_bound: "\<forall>z \<ge> 0. \<bar>f z\<bar> \<le> B" by (metis abs_of_nonneg)

  from assms(1)[unfolded almost_hom_def]
  obtain D where D_bound: "\<bar>f (m + n) - (f m + f n)\<bar> \<le> D" and D_nonneg: "0 \<le> D" for m n by (fastforce elim: boundedE)

  have bound: "m \<ge> 0 \<Longrightarrow> \<bar>f (-m)\<bar> \<le> \<bar>f 0\<bar> + B + D" for m
  proof-
    assume asm: "0 \<le> m"
    from D_bound[of "-m" m] have "\<bar>f (-m) - (- f(m))\<bar> \<le> D + \<bar>f 0\<bar>" by force
    with abs_triangle_ineq2[of "f (-m)" "- f m"] order.trans have "\<bar>f (-m)\<bar> - \<bar>f m\<bar> \<le> D + \<bar>f 0\<bar>" by auto
    with B_bound asm show ?thesis by fastforce
  qed

  let ?C = "\<bar>f 0\<bar> + B + D"
  show "bounded f"
  proof (rule boundedI)
    fix z
    show "\<bar>f z\<bar> \<le> ?C"
    proof (cases "z \<ge> 0")
      case True
      with B_bound B_nonneg D_nonneg show ?thesis by fastforce
    next
      case False
      hence "0 \<le> -z" by simp
      with bound[of "-z"] show ?thesis by fastforce
    qed
  qed
qed

corollary almost_hom_finite_range_iff:
  assumes "almost_hom f"
  shows "finite (range f) \<longleftrightarrow> finite (f ` {0..})"
proof (standard, goal_cases)
  case 1
  have "f ` {0..} \<subseteq> range f" by blast
  with 1 show ?case by (metis finite_subset) 
next
  case 2
  have "range (f o abs) = f ` {0..}" unfolding comp_def atLeast_def image_def by (metis UNIV_I abs_ge_zero abs_of_nonneg mem_Collect_eq)
  with almost_hom_bounded_comp_right_abs[OF assms, unfolded bounded_iff_finite_range] 2
  show ?case by argo
qed


lemma almost_hom_positive_lower_bound:
  assumes "almost_hom f" "infinite {f z | z :: int. 0 < f z \<and> 0 \<le> z}"
  shows "\<forall>D>0. \<exists>M>0. \<forall>m>0. (m + 1) * D \<le> f (m * M)"
proof (clarsimp, goal_cases)
  case (1 D)
  hence D_nonneg: "D \<ge> 0" by force
  from assms(1)[unfolded almost_hom_def]
  obtain C where C_bound: "\<bar>f (m + n) - (f m + f n)\<bar> \<le> C" and C_nonneg: "0 \<le> C" for m n by (fastforce elim: boundedE)

  let ?E = "C + D"
  from 1 C_nonneg have E_nonneg: "0 \<le> ?E" by simp
  from C_nonneg have D_le_E: "?E \<ge> D" by simp

  from int_set_infiniteD[OF assms(2)] mult_left_mono[OF E_nonneg, of 2]
  obtain u_M where "2 * ?E \<le> \<bar>u_M\<bar>" "u_M \<in> {f z |z. 0 < f z \<and> 0 \<le> z}" by fastforce
  then obtain M where M_bound: "2 * ?E \<le> \<bar>f M\<bar>" "0 < f M" and M_nonneg: "0 \<le> M" by blast

  have "(f (m * M + M) - (f (m * M) + f M)) \<ge> -C" for m by (metis C_bound abs_diff_le_iff minus_int_code(1,2))
  then have neg_E_bound: "(f (m * M + M) - (f (m * M) + f M)) \<ge> -?E" for m by (meson D_nonneg add_increasing2 minus_le_iff)

  have ineq: "m > 0 \<Longrightarrow> f (m * M) \<ge> (m + 1) * ?E" for m
  proof (induction m rule: int_induct[where ?k=1])
    case base
    from M_bound(1,2) show ?case by fastforce
  next
    case (step1 m)
    hence IH: "(m + 1) * ?E \<le> f (m * M)" by linarith
    have "(m + 1 + 1) * ?E = (m + 1) * ?E + 2 * ?E - ?E" by algebra
    also from M_bound(1,2) have "... \<le> (m + 1) * ?E + f M + - ?E" by fastforce
    also from IH have "... \<le> f (m * M) + f M + - ?E" by simp
    also have "... \<le> (f (m * M) + f M) + (f (m * M + M) - (f (m * M) + f M))" using add_left_mono[OF neg_E_bound] by blast
    also have "... = f ((m + 1) * M)" by (simp add: distrib_right)
    finally show ?case by blast
  next
    case (step2 i)
    then show ?case by linarith
  qed

  have final_ineq: "f (m * M) \<ge> (m + 1) * D" if asm: "m > 0" for m using ineq[OF asm] mult_left_mono[OF D_le_E, of "m + 1"] asm by linarith
  moreover have "M \<noteq> 0"
  proof
    assume asm: "M = 0"
    from final_ineq[OF M_bound(2), unfolded asm] have "f 0 * D + D \<le> f 0" by (simp add: distrib_right)
    moreover from 1 have one_le_D: "1 \<le> D" by fastforce 
    ultimately have "f 0 * D + 1 \<le> f 0" by force
    with one_le_D show False using M_bound(2) add1_zle_eq asm by force
  qed
  ultimately show ?case using M_nonneg by force
qed

lemma remove_bound_exceptions:
  assumes "\<forall>n\<ge>0. \<forall>m\<ge>0. n + m \<ge> (N :: int) \<longrightarrow> f n m \<le> (C :: int)"
  shows "\<exists>C. \<forall>n\<ge>0.\<forall>m\<ge>0. f n m \<le> C"
proof (cases "N \<ge> 0")
  case True
  define S where "S = (\<Union>n\<in>{0..<N}. \<Union>m\<in>{0..<N}. {f n m})"
  have bdd_above_S: "bdd_above S" unfolding S_def by fastforce
  have "\<forall>n\<in>{0..<N}.\<forall>m\<in>{0..<N}. f n m \<le> Sup S" using cSup_upper[OF _ bdd_above_S, of "f _ _"] S_def by blast
  hence b0: "\<forall>n\<in>{0..<N}.\<forall>m\<in>{0..<N}. f n m \<le> max C (Sup S)" by fastforce
  from assms True have b1: "\<forall>n\<ge>0.\<forall>m\<ge>N. f n m \<le> C" and b2: "\<forall>n\<ge>N.\<forall>m\<ge>0. f n m \<le> C" by simp+
  from b1 have "\<forall>n\<in>{0..<N}. \<forall>m\<ge>N. f n m \<le> max C (Sup S)" by fastforce
  with b0 have "\<forall>n\<in>{0..<N}. \<forall>m\<ge>0. f n m \<le> max C (Sup S)" by (meson atLeastLessThan_iff linorder_not_le)
  moreover from b2 have "\<forall>n\<ge>N.\<forall>m\<ge>0. f n m \<le> max C (Sup S)" by fastforce
  ultimately show ?thesis by (meson atLeastLessThan_iff linorder_not_le)
next
  case False
  hence "\<forall>n\<ge>0. \<forall>m\<ge>0. n + m \<ge> N" by fastforce
  with assms show ?thesis by auto
qed

lemma nonneg_int_InfI:
  assumes "({(0::int)..} \<inter> A) \<noteq> {}"
  shows "Inf ({0..} \<inter> A) \<in> ({0..} \<inter> A)"
proof-
  from assms have nat_A_not_empty: "nat ` ({0..} \<inter> A) \<noteq> {}" by blast

  have Inf_in: "int (Inf (nat ` ({0..} \<inter> A))) \<in> int ` nat ` ({0..} \<inter> A)" using nat_A_not_empty wellorder_InfI[of _ "nat ` ({0..} \<inter> A)"] by fast
  have int_nat_idem: "int ` nat ` ({0..} \<inter> A) = {0..} \<inter> A" by force
  have "Inf ({0..} \<inter> A) = int (Inf (nat ` ({0..} \<inter> A)))" 
  proof (rule cInf_eq_minimum, goal_cases)
    case 1
    with Inf_in int_nat_idem show ?case by argo
  next
    case (2 x)
    then show ?case by (metis IntD2 Int_commute atLeast_iff imageI le_nat_iff wellorder_Inf_le1)
  qed
  then show ?thesis using Inf_in int_nat_idem by argo
qed

lemma bdd_below_int_InfI:
  assumes "({(b::int)..} \<inter> A) \<noteq> {}"
  shows "Inf ({b..} \<inter> A) \<in> ({b..} \<inter> A)"
proof (cases "b \<ge> 0")
  case True
  then have "({b..} \<inter> A) = {0..} \<inter> ({b..} \<inter> A)" by fastforce
  with assms nonneg_int_InfI show ?thesis by metis
next
  case False
  then have partition: "({b..} \<inter> A) = ({0..} \<inter> A) \<union> ({b..<0} \<inter> A)" by fastforce
  have bdd_below: "bdd_below ({0..} \<inter> A)" "bdd_below ({b..<0} \<inter> A)" by simp+
  then show ?thesis 
  proof (cases "({0..} \<inter> A) \<noteq> {} \<and> ({b..<0} \<inter> A) \<noteq> {}")
    case True
    hence asm: "({0..} \<inter> A) \<noteq> {}" "({b..<0} \<inter> A) \<noteq> {}" by blast+
    have finite: "finite ({b..<0} \<inter> A)" by blast
    have "(x :: int) \<le> y \<Longrightarrow> inf x y = x" for x y by (simp add: inf.order_iff)
    have "Inf ({b..} \<inter> A) = inf (Inf ({0..} \<inter> A)) (Inf ({b..<0} \<inter> A))" by (metis cInf_union_distrib asm bdd_below partition)
    moreover have "Inf ({b..<0} \<inter> A) \<in> ({b..} \<inter> A)" using Min_in[OF finite asm(2), folded cInf_eq_Min[OF finite asm(2)]] partition by blast
    moreover have "Inf ({0..} \<inter> A) \<in> ({b..} \<inter> A)" using nonneg_int_InfI[OF asm(1)] partition by blast
    moreover have "inf (Inf ({0..} \<inter> A)) (Inf ({b..<0} \<inter> A)) \<in> {Inf ({0..} \<inter> A), Inf ({b..<0} \<inter> A)}"
    proof (standard, goal_cases)
      case 1
      from inf.order_iff[of "Inf ({b..<0} \<inter> A)" "Inf ({0..} \<inter> A)"]
      have "inf (Inf ({b..<0} \<inter> A)) (Inf ({0..} \<inter> A)) \<noteq> (Inf ({b..<0} \<inter> A)) \<Longrightarrow> Inf ({0..} \<inter> A) \<le> Inf ({b..<0} \<inter> A)" by simp
      with 1 have "Inf ({0..} \<inter> A) \<le> Inf ({b..<0} \<inter> A)" by (simp add: inf.commute)
      then show ?case using inf.order_iff by metis
    qed
    ultimately show ?thesis by force
  next
    case False
    with partition have "({b..} \<inter> A) = ({0..} \<inter> A) \<or> ({b..} \<inter> A) = ({b..<0} \<inter> A)" by auto
    then show ?thesis
    proof (standard, goal_cases)
      case 1
      with assms nonneg_int_InfI show ?case by auto
    next
      case 2
      hence finite: "finite ({b..} \<inter> A)" by simp
      then show ?case using Min_in[OF finite assms, folded cInf_eq_Min[OF finite assms]] by blast
    qed
  qed
qed

end