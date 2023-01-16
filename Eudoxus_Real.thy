theory Eudoxus_Real
  imports Almost_Homomorphism HOL.Archimedean_Field "HOL-Eisbach.Eisbach"
begin

definition real_rel :: "(int \<Rightarrow> int) \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> bool" (infix "\<sim>" 50) where 
  "f \<sim> g \<equiv> almost_hom f \<and> almost_hom g \<and> bounded (\<lambda>n. f n - g n)"

(*
lemma equiv_real_rel: "equiv (Collect almost_hom) real_rel"
proof (rule equivI)
  show "refl_on (Collect almost_hom) real_rel" unfolding real_rel_def almost_hom_def bounded_def by (rule refl_onI, auto)
  show "sym real_rel" unfolding real_rel_def by (rule symI, clarsimp) (force dest: bounded_uminus) 
  show "trans real_rel" unfolding real_rel_def by (rule transI, clarsimp) (force dest: bounded_add)
qed

lemma equiv_real_rel_def: "refl_on (Collect almost_hom) real_rel" "sym real_rel" "trans real_rel"
  using equivE[OF equiv_real_rel] by argo+
*)

lemma real_rel_equivp:
  "part_equivp real_rel"
proof (auto intro!: part_equivpI)
  show "\<exists>x. x \<sim> x" unfolding real_rel_def almost_hom_def bounded_def by fast
  show "symp (\<sim>)"  unfolding real_rel_def by (rule sympI) (force dest: bounded_uminus) 
  show "transp (\<sim>)"  unfolding real_rel_def by (rule transpI) (force dest: bounded_add)
qed

quotient_type real = "(int \<Rightarrow> int)" / partial: real_rel
  by (rule real_rel_equivp)

lemma real_quot_type: "quot_type (\<sim>) Abs_real Rep_real"
  using Rep_real Abs_real_inverse Rep_real_inverse Rep_real_inject real_rel_equivp by (auto intro!: quot_type.intro)

lemma almost_hom_reflI: 
  assumes "almost_hom f"
  shows "f \<sim> f"
  unfolding real_rel_def by (fastforce simp: assms bounded_constant)

lemma refl_almost_homI: 
  assumes "f \<sim> f"
  shows "almost_hom f"
  using assms unfolding real_rel_def by blast

lemma abs_real_inject:
  assumes "f \<sim> f" "g \<sim> g" "abs_real f = abs_real g"
  shows "f \<sim> g"
  using Quotient_rel[OF Quotient_real] assms by blast

lemmas abs_real_eqI = Quotient_rel_abs[OF Quotient_real]
lemmas rep_real_inverse = Quotient_rep_abs[OF Quotient_real, intro!]

lemmas real_rel_sym = Quotient_symp[OF Quotient_real, THEN sympD]
lemmas real_rel_trans = Quotient_transp[OF Quotient_real, THEN transpD]
lemmas abs_rep = Quotient_abs_rep[OF Quotient_real, simp]
lemmas rel_rep = Quotient_rel_rep[OF Quotient_real, simp]

lemmas real_rel_reflI' = real_rel_sym[THEN real_rel_trans, THEN TrueE[simplified, of "(\<lambda>x. x \<sim> x) _"]] real_rel_trans[OF _ real_rel_sym, THEN TrueE[simplified, of "(\<lambda>x. x \<sim> x) _"]]

lemma real_eqI:
  assumes "\<And>n. \<bar>rep_real x n - rep_real y n\<bar> \<le> C"
  shows "x = y"
  using assms 
  by (subst Quotient_rel_rep[OF Quotient_real, THEN iffD1, unfolded real_rel_def], simp add: refl_almost_homI)
     (auto intro: boundedI)

instantiation real :: "{zero, plus, minus, uminus}"
begin

quotient_definition
  "0 :: real" is "abs_real (\<lambda>_. 0)" .

declare almost_hom_reflI[OF almost_hom_zero, simp]

fun real_add where
  "real_add (f :: int \<Rightarrow> int) g = (\<lambda>z. f z + g z)"

quotient_definition
  "(+) :: (real \<Rightarrow> real \<Rightarrow> real)" is real_add 
proof (simp)
  fix x x' y y'
  assume [unfolded real_rel_def]: "x \<sim> x'" "y \<sim> y'"
  hence rel_x: "almost_hom x" "almost_hom x'" "bounded (\<lambda>z. x z - x' z)" and rel_y: "almost_hom y" "almost_hom y'" "bounded (\<lambda>z. y z - y' z)" by blast+
  show "(\<lambda>z. x z + y z) \<sim> (\<lambda>z. x' z + y' z)" unfolding real_rel_def
    by (simp add: almost_hom_add[OF rel_x(1) rel_y(1)] almost_hom_add[OF rel_x(2) rel_y(2)])
       (rule back_subst[of bounded, OF bounded_add[OF rel_x(3) rel_y(3)]], fastforce)
qed

lemmas real_rel_add = apply_rsp'[OF plus_real.rsp, THEN rel_funD, intro]

lemma real_add_abs: 
  assumes "a \<sim> a" "b \<sim> b"
  shows "abs_real a + abs_real b = abs_real (real_add a b)" "real_add a b \<sim> real_add a b"
  by (auto simp add: plus_real_def assms simp del: real_add.simps intro!: abs_real_eqI)

fun real_uminus where
  "real_uminus (f :: int \<Rightarrow> int) = - f"

quotient_definition
  "(uminus) :: (real \<Rightarrow> real)" is real_uminus
proof (simp)
  fix x x'
  assume [unfolded real_rel_def]: "x \<sim> x'"
  hence rel_x: "almost_hom x" "almost_hom x'" "bounded (\<lambda>z. x z - x' z)" by blast+
  show "-x \<sim> -x'" unfolding real_rel_def fun_Compl_def 
    by (auto simp add: rel_x(1,2)[THEN almost_hom_uminus_comp])
       (rule back_subst[of bounded, OF bounded_uminus[OF rel_x(3)]], fastforce)
qed

lemmas real_rel_uminus = apply_rsp'[OF uminus_real.rsp, simplified, intro]

lemma real_uminus_abs: 
  assumes "a \<sim> a"
  shows "-abs_real a = abs_real (- a)" "- a \<sim> - a"
  by (auto simp add: uminus_real_def assms intro!: abs_real_eqI)

definition "x - (y::real) = x + - y"

instance ..
end

lemma [simp]: assumes "f \<sim> f"
  shows "abs_real (-f) = - abs_real f" by (simp add: real_uminus_abs(1)[OF assms])



instance real :: ab_group_add
proof
  fix x y z :: real
  show "x + y + z = x + (y + z)" by (induct x, induct y, induct z, auto simp add: real_add_abs simp del: real_add.simps, simp add: add.assoc)
  show "x + y = y + x" by (induct x, induct y, simp add: real_add_abs, simp only: add.commute)
  show "0 + x = x" by (induct x, simp add: real_add_abs zero_real_def del: real_add.simps, simp)
  show "-x + x = 0" by (induct x, simp only: real_add_abs real_uminus_abs zero_real_def, simp)
qed (simp add: minus_real_def)

lemma real_diff_abs:
  assumes "g \<sim> g" "f \<sim> f"
  shows "abs_real (real_add g (-f)) = abs_real g - abs_real f" 
  using assms real_add_abs(1) real_uminus_abs(2) by fastforce

instantiation real :: "{one, times}"
begin

quotient_definition
  "1 :: real" is "abs_real id" .

declare almost_hom_reflI[OF almost_hom_one, simp]

fun real_mult :: "(int \<Rightarrow> int) \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int"where
  "real_mult f g = f o g"

quotient_definition
  "(*) :: real \<Rightarrow> real \<Rightarrow> real" is real_mult
proof (simp)
  fix x x' y y'
  assume [unfolded real_rel_def]: "x \<sim> x'" "y \<sim> y'"
  hence rel_x: "almost_hom x" "almost_hom x'" "bounded (\<lambda>z. x z - x' z)" and rel_y: "almost_hom y" "almost_hom y'" "bounded (\<lambda>z. y z - y' z)" by blast+

  from rel_x(2)[unfolded almost_hom_def] 
  obtain C where x'_bound: "\<bar>x' (m + n) - (x' m + x' n)\<bar> \<le> C" for m n by (fastforce elim: boundedE)

  from almost_hom_linear_bound[OF rel_x(2)]
  obtain A B where x'_lin_bound: "\<bar>x' n\<bar> \<le> A * \<bar>n\<bar> + B" "0 \<le> A" "0 \<le> B" for n by blast

  from rel_y(3)[unfolded almost_hom_def]
  obtain C' where y_y'_bound: "\<bar>y z - y' z\<bar> \<le> C'" for z by (fastforce elim: boundedE)

  have "bounded (\<lambda>z. x' (y z) - x' (y' z))" 
  proof (rule boundedI)
    fix z
    from x'_bound[of "y z - y' z" "y' z"] have "\<bar>x' (y z) - x' (y' z)\<bar> \<le> \<bar>x' (y z - y' z)\<bar> + C" by fastforce
    also from x'_lin_bound(1) have "... \<le> A * \<bar>y z - y' z\<bar> + B + C" by force
    also from mult_left_mono[OF y_y'_bound[of z] x'_lin_bound(2)] have "... \<le> A * C' + B + C" by fastforce
    finally show "\<bar>x' (y z) - x' (y' z)\<bar> \<le> A * C' + B + C" by blast
  qed
 
  from bounded_add[OF bounded_comp(1)[OF rel_x(3), of y, unfolded comp_def] this]
  have "bounded (\<lambda>z. x (y z) - x' (y' z))" by force
  thus "(x \<circ> y) \<sim> (x' \<circ> y')" unfolding real_rel_def by (simp add: almost_hom_comp[OF rel_x(1) rel_y(1)] almost_hom_comp[OF rel_x(2) rel_y(2)])
qed

lemmas real_rel_mult = apply_rsp'[OF times_real.rsp, THEN rel_funD, intro]

lemma real_mult_abs: 
  assumes "a \<sim> a" "b \<sim> b"
  shows "abs_real a * abs_real b = abs_real (real_mult a b)" "real_mult a b \<sim> real_mult a b"
  by (auto simp add: times_real_def assms simp del: real_mult.simps intro!: abs_real_eqI)

lemma real_mult_commute:
  assumes "a \<sim> a" "b \<sim> b"
  shows "abs_real (real_mult a b) = abs_real (real_mult b a)"
  by (auto intro!: abs_real_eqI) (metis almost_hom_comp real_rel_def almost_hom_comp_commute assms[THEN refl_almost_homI])

instance ..
end

lemmas real_ring_simps = real_add.simps real_uminus.simps real_mult.simps
lemma minus_one_real_def: "-1 = abs_real (- id)" using one_real_def by force

lemma non_zero_realI:
  assumes "f \<sim> f" "\<not> bounded f"
  shows "0 \<noteq> abs_real f"
proof
  assume "0 = abs_real f"
  hence "f \<sim> (\<lambda>_. 0)" unfolding zero_real_def by (auto simp: abs_real_inject[OF assms(1)])
  with assms(2) show False unfolding real_rel_def by fastforce
qed

lemma non_zero_realE:
  assumes "f \<sim> f" "0 \<noteq> abs_real f"
  shows "\<not> bounded f"
proof
  assume asm: "bounded f"
  have "f \<sim> (\<lambda>_.0)" by (auto simp: asm almost_hom_zero real_rel_def refl_almost_homI[OF assms(1)])
  with assms(2) show False unfolding zero_real_def by (simp add: abs_real_eqI)
qed

lemma non_zero_iff:
  assumes "f \<sim> f"
  shows "0 \<noteq> abs_real f \<longleftrightarrow> \<not>(f \<sim> (\<lambda>_.0))"
  unfolding zero_real_def by (auto simp add: abs_real_eqI) (simp add: abs_real_inject assms)

instance real :: comm_ring_1
proof
  fix x y z :: real
  show "x * y * z = x * (y * z)" by (induct x, induct y, induct z, simp add: real_mult_abs del: real_mult.simps, simp add: comp_assoc)
  show "x * y = y * x" by (induct x, induct y, simp add: real_mult_abs real_mult_commute del: real_mult.simps)
  show "1 * x = x" by (induct x, simp add: one_real_def real_mult_abs del: real_mult.simps, simp)
  show "(x + y) * z = x * z + y * z" by (induct x, induct y, induct z, simp add: real_mult_abs real_add_abs del: real_mult.simps real_add.simps, simp add: comp_def)
  show "(0 :: real) \<noteq> (1 :: real)" unfolding one_real_def by (subst id_apply, rule non_zero_realI, auto simp: bounded_iff_finite_range)
qed

declare almost_hom_reflI[OF almost_hom_scale, simp]

lemma real_of_nat:
  "of_nat n = abs_real ((*) (of_nat n))"
proof (induction n)
  case 0
  then show ?case by (simp add: zero_real_def)
next
  case (Suc n)
  then show ?case by (simp add: real_add_abs one_real_def distrib_right)
qed

declare almost_hom_reflI[OF almost_hom_uminus, simp]

lemma real_of_int:
  "of_int z = abs_real ((*) z)"
proof (induction z rule: int_induct[where ?k=0])
  case base
  then show ?case by (simp add: zero_real_def)
next
  case (step1 i)
  then show ?case by (simp add: one_real_def real_add_abs distrib_right)
next
  case (step2 i)
  then show ?case by (simp add: one_real_def real_add_abs real_uminus_abs minus_real_def fun_Compl_def left_diff_distrib)
qed

instance real :: ring_char_0
proof
  show "inj (\<lambda>n. of_nat n :: real)"
  proof (subst real_of_nat, standard, goal_cases)
    case (1 x y)
    then have "((*) (int x)) \<sim> ((*) (int y))" by (simp add: abs_real_inject)
    hence "bounded (\<lambda>z. (int x - int y) * z)" unfolding real_rel_def by (simp add: left_diff_distrib)
    then obtain C where bound: "\<bar>(int x - int y) * z\<bar> \<le> C" and C_nonneg: "0 \<le> C" for z by (blast elim: boundedE)
    from bound have "\<bar>int x - int y\<bar> * \<bar>z\<bar> \<le> C" for z by (simp add: abs_mult)
    from this[of "C + 1"] C_nonneg have ineq: "\<bar>int x - int y\<bar> * (C + 1) \<le> C" by force
    show ?case
    proof (rule ccontr)
      assume "x \<noteq> y"
      hence "1 \<le> \<bar>int x - int y\<bar>" by force
      from order.trans[OF mult_right_mono[OF this] ineq] C_nonneg show False by simp
    qed
  qed
qed



instantiation real :: "{ord, abs, sgn}"
begin

fun real_positive :: "(int \<Rightarrow> int) \<Rightarrow> bool" where
  "real_positive f = (\<forall>C \<ge> 0. \<exists>N. \<forall>p \<ge> N. f p \<ge> C)"

fun real_negative :: "(int \<Rightarrow> int) \<Rightarrow> bool" where
  "real_negative f = (\<forall>C \<ge> 0. \<exists>N. \<forall>p \<ge> N. f p \<le> -C)"

lemmas real_signs = real_positive.simps real_negative.simps

lift_definition real_positive :: "(int \<Rightarrow> int) \<Rightarrow> bool" is real_positive oops

lemma pos_invariant:
  assumes "f \<sim> g" "\<forall>C \<ge> 0. \<exists>N. \<forall>p\<ge>N. C \<le> f p"
  shows "\<forall>C \<ge> 0. \<exists>N. \<forall>p\<ge>N. C \<le> g p"
proof (clarify)
  fix D assume D_nonneg: "0 \<le> (D :: int)"
  from assms(1) obtain C where C_bound: "\<bar>f p - g p\<bar> \<le> C" and C_nonneg: "0 \<le> C" for p 
    unfolding real_rel_def by (fastforce elim: boundedE)
  from C_bound have C_bound': "f p \<le> g p + C" for p using abs_diff_le_iff by blast
  from D_nonneg C_nonneg assms(2) obtain N where "\<forall>p \<ge> N. D + C \<le> f p" by fastforce
  with C_bound' have "\<forall>p \<ge> N. D + C \<le> g p + C" using order.trans by fast
  then have "\<forall>p \<ge> N. D \<le> g p" by simp
  thus "\<exists>N. \<forall>p\<ge>N. D \<le> g p" by blast
qed

lemma neg_invariant:
  assumes "f \<sim> g" "\<forall>C \<ge> 0. \<exists>N. \<forall>p\<ge>N. f p \<le> -C"
  shows "\<forall>C \<ge> 0. \<exists>N. \<forall>p\<ge>N. g p \<le> -C"
proof (clarify)
  fix D assume D_nonneg: "0 \<le> (D :: int)"
  from assms(1) obtain C where C_bound: "\<bar>f p - g p\<bar> \<le> C" and C_nonneg: "0 \<le> C" for p 
    unfolding real_rel_def by (fastforce elim: boundedE)
  from C_bound have C_bound': "g p - C \<le> f p" for p using abs_diff_le_iff by blast
  from D_nonneg C_nonneg assms(2) obtain N where "\<forall>p \<ge> N. f p \<le> -(C + D)" by (meson add_increasing)
  with C_bound' have "\<forall>p \<ge> N. g p - C \<le> -(C + D)" using order.trans by blast
  then have "\<forall>p \<ge> N. g p \<le> -D" by simp
  thus "\<exists>N. \<forall>p\<ge>N. g p \<le> -D" by blast
qed

lemma real_positive_iff:
  assumes "u \<sim> u"
  shows "infinite {u z | z. 0 < u z \<and> 0 \<le> z} = (\<forall>C \<ge> 0. \<exists>N. \<forall>p \<ge> N. u p \<ge> C)"
proof (standard, goal_cases)
  case 1
  from assms[unfolded real_rel_def]
  have almost_hom: "almost_hom u" by blast
  then obtain D where D_bound: "\<bar>u (m + n) - (u m + u n)\<bar> < D" "0 < D" for m n by (fastforce simp: almost_hom_def elim: boundedE2)

  from almost_hom_positive_lower_bound[OF almost_hom 1] D_bound(2)
  obtain M where M_bound: "\<forall>m>0. (m + 1) * D \<le> u (m * M)" "0 < M" by blast

  define g where "g = (\<lambda>z. u ((z div M) * M))"

  define E where "E = Sup ((abs o u) ` {z. 0 \<le> z \<and> z < M})"
  
  have E_bound: "\<bar>u (z mod M)\<bar> \<le> E" for z
  proof -
    have "(z mod M) \<in> {z. 0 \<le> z \<and> z < M}" by (simp add: M_bound(2))
    hence "\<bar>u (z mod M)\<bar> \<in> (abs o u) ` {z. 0 \<le> z \<and> z < M}" by fastforce
    thus "\<bar>u (z mod M)\<bar> \<le> E" unfolding E_def by (simp add: le_cSup_finite)
  qed
  hence E_nonneg: "0 \<le> E" by fastforce

  have diff_bound: "\<bar>u z - g z\<bar> \<le> E + D" for z
  proof-
    let ?d = "z div M" and ?r = "z mod M"
    have z_is: "z = ?d * M + ?r" by presburger
    then have "\<bar>u z - g z\<bar> = \<bar>u (?d * M + ?r) - g (?d * M + ?r)\<bar>" by argo
    also have "... = \<bar>(u (?d*M + ?r) - (u (?d * M) + u ?r)) + (u (?d * M) + u ?r) - g (?d * M + ?r)\<bar>" by auto
    also have "... = \<bar>u ?r + (u (?d*M + ?r) - (u (?d * M) + u ?r))\<bar>" unfolding g_def by force
    also from D_bound(1)[of "?d*M" "?r"] have "... \<le> \<bar>u ?r\<bar> + D" by linarith
    also from E_bound[of z] have "... \<le> E + D" by simp
    finally show "\<bar>u z - g z\<bar> \<le> E + D" .
  qed

  show ?case
  proof (clarsimp)
    fix C assume C_nonneg: "0 \<le> (C :: int)"

    define n where "n = (E + D + C) div D"
    hence zero_less_n: "n > 0" using D_bound(2) E_nonneg C_nonneg using pos_imp_zdiv_pos_iff by fastforce

    from diff_strict_left_mono[OF pos_mod_bound[OF D_bound(2), of "E + D + C"], of "E + D + C"] 
    have "E + C < E + D + C - (E + D + C) mod D" by linarith
    also from div_mod_decomp_int[of "E + D + C" D] have "... = n * D" unfolding n_def by algebra
    finally have n_ineq: "(n + 1) * D > E + D + C" by (simp add: add.commute distrib_right)

    have "p > n * M \<Longrightarrow> C \<le> u p" for p
    proof (goal_cases)
      case 1
      hence nM_le_p: "p \<ge> n * M" by fastforce
      let ?d = "p div M" and ?r = "p mod M"
      from 1 zero_less_n M_bound(2) have d_pos:"?d > 0" by (metis dual_order.strict_iff_not int_one_le_iff_zero_less leI mult.commute mult_less_cancel_left2 order_less_trans pos_imp_zdiv_pos_iff)
      from nM_le_p have n_le_d: "?d \<ge> n" using zdiv_mono1 M_bound(2) by fastforce
      from n_ineq have "E + D + C < (n + 1) * D" .
      also have "... \<le> (?d + 1) * D" by (simp add: D_bound(2) n_le_d)
      also from M_bound d_pos have "... \<le> g p" unfolding g_def by blast
      finally have "E + D + C < g p" .
      with diff_bound[of p] have "\<bar>u p - g p\<bar> + C < g p" by fastforce
      then show ?case by fastforce
    qed
    thus "\<exists>N. \<forall>p\<ge>N. C \<le> u p" using add1_zle_eq by blast
  qed
next
  case 2
  show ?case 
  proof (rule int_set_infiniteI, clarsimp)
    fix C assume C_nonneg: "0 \<le> (C :: int)"
    with 2 have "\<exists>z \<ge> 0. (C + 1) \<le> u z" by (metis add_increasing2 nle_le zero_less_one_class.zero_le_one)
    with C_nonneg have "\<exists>z \<ge> 0. C \<le> u z \<and> 0 < u z" by fastforce
    with C_nonneg show "\<exists>N\<ge>C. \<exists>z. N = u z \<and> 0 < u z \<and> 0 \<le> z" by blast
  qed
qed

lemma real_negative_iff:
  assumes "u \<sim> u"
  shows "infinite {u z | z. 0 > u z \<and> 0 \<le> z} = (\<forall>C \<ge> 0. \<exists>N. \<forall>p \<ge> N. u p \<le> -C)"
proof (standard, goal_cases)
  case 1
  from assms[unfolded real_rel_def]
  have almost_hom: "almost_hom u" by blast
  from 1 have "infinite {u z | z. 0 < -u z \<and> 0 \<le> z}" by simp
  moreover have "inj (uminus :: int \<Rightarrow> int)" by simp
  moreover have "{-u z | z. 0 < -u z \<and> 0 \<le> z} = uminus ` {u z | z. 0 < -u z \<and> 0 \<le> z}" by blast
  ultimately have "infinite {-u z | z. 0 < -u z \<and> 0 \<le> z}" using finite_imageD by fastforce
  with real_positive_iff[OF almost_hom_reflI[OF almost_hom_uminus_comp[OF almost_hom]]] show ?case by fastforce 
next
  case 2
  from assms[unfolded real_rel_def]
  have almost_hom: "almost_hom u" by blast
  from 2 real_positive_iff[OF almost_hom_reflI[OF almost_hom_uminus_comp[OF almost_hom]]] 
  have "infinite {-u z | z. 0 < -u z \<and> 0 \<le> z}" by fastforce
  moreover have "inj (uminus :: int \<Rightarrow> int)" by simp
  moreover have "{-u z | z. 0 < -u z \<and> 0 \<le> z} = uminus ` {u z | z. 0 < -u z \<and> 0 \<le> z}" by blast
  ultimately show "infinite {u z | z. 0 > u z \<and> 0 \<le> z}" using finite_imageD by fastforce
qed

fun real_sgn :: "(int \<Rightarrow> int) \<Rightarrow> (int \<Rightarrow> int)" where 
  "real_sgn f = (if real_positive f then id else 
                                    if real_negative f then -id else (\<lambda>_.0))"

lemma real_sgn_range:
  shows "real_sgn f \<in> {-id, (\<lambda>_.0), id}" by simp

lemma sgn_no_overlap: "\<not> (real_positive f \<and> real_negative f)"
proof (standard, goal_cases)
  case 1
  then show ?case
  proof (auto, goal_cases)
    case 1
    from 1(1)
    obtain N_x where N_u_is: "\<forall>p\<ge>N_x. 1 \<le> f p" by fastforce
    from 1(2)
    obtain N_x' where N_u'_is: "\<forall>p\<ge>N_x'. 0 \<le> - f p" by fastforce
  
    from N_u_is N_u'_is have "\<forall>p\<ge>max N_x N_x'. 1 \<le> 0" by fastforce
    thus False by fastforce
  qed
qed


lemma real_pos_impl_not_neg:
  assumes "f \<sim> f"
  shows "real_positive f \<Longrightarrow> \<not> real_negative f"
  using sgn_no_overlap by blast


lemma real_neg_impl_not_pos:
  assumes "f \<sim> f"
  shows "real_negative f \<Longrightarrow> \<not> real_positive f"
  using sgn_no_overlap by blast

lemma sgn_non_zero:
  assumes "f \<sim> f" "\<not>(f \<sim> (\<lambda>_. 0))"
  shows "real_positive f \<or> real_negative f"
proof (rule disjCI)

  assume "\<not> real_negative f"
  with real_negative_iff[OF assms(1)]
  have "finite {f z |z. f z < 0 \<and> 0 \<le> z}" by fastforce
  moreover have "{f z |z. f z \<le> 0 \<and> 0 \<le> z} \<subseteq> insert 0 {f z |z. f z < 0 \<and> 0 \<le> z}" by fastforce
  ultimately have finite_N: "finite {f z |z. f z \<le> 0 \<and> 0 \<le> z}" by (meson finite.insertI infinite_super)

  from non_zero_iff[OF assms(1)] assms(2) have "\<not>bounded f" by (simp add: non_zero_realE[OF assms(1)])
  then have  "infinite (range (f))" unfolding bounded_iff_finite_range by simp
  with almost_hom_finite_range_iff[OF refl_almost_homI[OF assms(1)], unfolded atLeast_def]
  have "infinite {f z |z. 0 \<le> z}" by (simp add: setcompr_eq_image)
  then have "infinite ({f z |z. 0 \<le> z} - {f z |z. f z \<le> 0 \<and> 0 \<le> z})" by (force simp: finite_N)
  moreover have "{f z |z. f z > 0 \<and> 0 \<le> z} = {f z |z. 0 \<le> z} - {f z |z. f z \<le> 0 \<and> 0 \<le> z}" by force
  ultimately have "infinite {f z |z. f z > 0 \<and> 0 \<le> z}" by argo
  with real_positive_iff[OF assms(1)] show "real_positive f" by simp
qed

lemma sgn_uminus_np: 
  assumes "f \<sim> f"
  shows "real_negative (-f) = real_positive f"
  by auto

lemma sgn_uminus_pn: 
  assumes "f \<sim> f"
  shows "real_positive (-f) = real_negative f"
  by (auto) (fastforce+)

lemma real_pos_impl: 
  assumes "x \<sim> y"
  shows "real_positive x \<Longrightarrow> real_positive y"
proof (rule ccontr, auto, goal_cases)
  case (1 D)
  from assms have refls: "x \<sim> x" "y \<sim> y" using real_rel_reflI' by blast+
  from assms obtain C where bounds: "\<forall>n. \<bar>x n - y n\<bar> \<le> C" "0 \<le> C" unfolding real_rel_def by (blast elim: boundedE)
  from 1(1,2) bounds(2) obtain N where "\<forall>p\<ge>N. D + C \<le> x p" by fastforce
  with bounds(1) have "\<forall>p\<ge>N. D + \<bar>x p - y p\<bar> \<le> x p" by (meson add_le_cancel_left dual_order.trans)
  hence "\<forall>p\<ge>N. D \<le> y p" by force
  with 1(3) show ?case by blast
qed

lemma real_neg_impl:
  assumes "x \<sim> y"
  shows "real_negative x \<Longrightarrow> real_negative y"
  using real_pos_impl real_rel_reflI'[THEN sgn_uminus_pn[symmetric], OF assms(1,1)] assms by blast

quotient_definition
  "(sgn :: real \<Rightarrow> real)" is "real_sgn"
  by (metis almost_hom_one almost_hom_reflI almost_hom_zero real_neg_impl real_pos_impl real_rel_sym real_sgn.elims real_uminus_abs(2))

lemma sgn_zero_iff:
  shows "sgn x = (0 :: real) \<longleftrightarrow> x = 0"
proof (standard, rule ccontr, goal_cases)
  case 1
  from 1(2) have "\<not>(rep_real x \<sim> (\<lambda>_.0))" unfolding zero_real_def using abs_real_eqI by fastforce 
  then have "sgn x \<in> abs_real ` {id :: (int \<Rightarrow> int), -id}" unfolding sgn_real_def using sgn_non_zero[of "rep_real x"] by (fastforce simp del: real_signs)
  moreover have "abs_real id = 1" using one_real_def by simp
  moreover have "abs_real (real_uminus id) = -1" using real_uminus_abs[of id] almost_hom_one[THEN almost_hom_reflI] one_real_def by fastforce
  moreover have "1 \<noteq> (0 :: real)" by simp
  moreover have "-1 \<noteq> (0 :: real)" by simp
  ultimately have "sgn x \<noteq> 0" by fastforce
  with 1(1) show False by blast
next
  case 2
  hence asm: "rep_real x \<sim> (\<lambda>_. 0)" unfolding zero_real_def id_apply by force
  from asm have "bounded (rep_real x)" by (force simp: real_rel_def dest: bounded_uminus)
  then obtain C where bounded: "\<bar>rep_real x z\<bar> \<le> C" and C_nonneg: "0 \<le> C" for z by (blast elim: boundedE)  
  have "\<not> real_positive (rep_real x) \<and> \<not> real_negative (rep_real x)"
  proof (standard, all \<open>standard\<close>, goal_cases)
    case 1
    from add_mono[OF C_nonneg zero_le_one] 1
    obtain N where "(C + 1) \<le> rep_real x N" by auto
    with bounded[of N] show False by force
  next
    case 2
    from add_mono[OF C_nonneg zero_le_one] 2
    obtain N where "rep_real x N \<le> -(C + 1)" by fastforce
    with bounded[of N] show False by force
  qed
  then show "sgn x = 0" unfolding sgn_real_def by (simp add: zero_real_def del: real_signs)
qed

lemma sgn_pos_iff: "sgn x = 1 \<longleftrightarrow> real_positive (rep_real x)"
  unfolding sgn_real_def using one_real_def zero_real_def by force

lemma sgn_pos_iff2: 
  assumes "f \<sim> f"
  shows "sgn (abs_real f) = 1 \<longleftrightarrow> real_positive f"
  by (metis abs_real_inject abs_rep assms real_pos_impl rel_rep sgn_pos_iff)

lemma real_sgn_pos_iff: 
  assumes "f \<sim> f"
  shows "real_sgn f = id \<longleftrightarrow> real_positive f"
  by (metis id_apply minus_one_real_def one_neq_neg_one one_neq_zero one_real_def real_sgn.elims)

lemma sgn_neg_iff: "sgn x = -1 \<longleftrightarrow> real_negative (rep_real x)"
  unfolding sgn_real_def using sgn_no_overlap one_real_def zero_real_def by (force simp del: real_signs)

lemma sgn_neg_iff2: 
  assumes "f \<sim> f"
  shows "sgn (abs_real f) = -1 \<longleftrightarrow> real_negative f"
  by (metis abs_real_inject abs_rep assms real_neg_impl rel_rep sgn_neg_iff)

lemma real_sgn_neg_iff: 
  assumes "f \<sim> f"
  shows "real_sgn f = - id \<longleftrightarrow> real_negative f"
  by (metis id_apply minus_one_real_def neg_equal_0_iff_equal one_neq_neg_one one_real_def real_sgn.elims sgn_no_overlap zero_real_def)


lemma sgn_add:
  assumes "sgn x = (1 :: real)" "sgn y = 1"
  shows "sgn (x + y) = 1"
proof-
  from assms have positive: "real_positive (rep_real x)" "real_positive (rep_real y)" by (simp add: sgn_pos_iff)+

  have "real_add (rep_real x) (rep_real y) \<sim> rep_real (x + y)" by (induct x, induct y, simp add: plus_real_def Quotient3_real real_add_abs(2) rep_abs_rsp del: real_add.simps)
  then obtain B where "\<bar>(rep_real x) z + (rep_real y) z - rep_real (x + y) z\<bar> \<le> B" and B_nonneg: "0 \<le> B" for z unfolding real_rel_def by (fastforce elim: boundedE)
  hence bound: "(rep_real x) z + (rep_real y) z \<le> B + rep_real (x + y) z" for z by (meson abs_le_D1 diff_le_eq)
  
  have "\<forall>C\<ge>0. \<exists>N. \<forall>z\<ge>N. C \<le> rep_real (x + y) z"
  proof (clarsimp)
    fix C assume asm: "0 \<le> (C :: int)"
    from positive(1) asm B_nonneg obtain Nx where Nx_bound: "\<forall>p\<ge>Nx. C + B \<le> rep_real x p" by fastforce
    from positive(2) asm B_nonneg obtain Ny where Ny_bound: "\<forall>p\<ge>Ny. C + B \<le> rep_real y p" by fastforce
    let ?N = "max Nx Ny"
    from Nx_bound Ny_bound asm B_nonneg have "\<forall>p\<ge>?N. C + B \<le> rep_real x p + rep_real y p" by fastforce
    with bound B_nonneg have "\<forall>p\<ge>?N. C \<le> rep_real (x + y) p" by (fastforce dest: order.trans)
    thus "\<exists>N. \<forall>p\<ge>N. C \<le> rep_real (x + y) p" by blast
  qed
  thus ?thesis unfolding sgn_real_def one_real_def by fastforce
qed
  
lemma sgn_uminus:
  shows "sgn x = (1 :: real) \<longleftrightarrow> sgn (-x) = -1"
proof-
  have "(real_uminus (rep_real x)) \<sim> rep_real (-x)" using Quotient_real Quotient_rel by fastforce 
  then obtain B where bound: "\<bar>-rep_real x z - rep_real (-x) z\<bar> \<le> B" and B_nonneg: "0 \<le> B" for z unfolding real_rel_def by (fastforce elim: boundedE)
  from bound have B_bound1: "rep_real x z \<le> B - rep_real (-x) z" for z by (simp add: abs_le_iff add.commute add_le_imp_le_diff)
  from bound have B_bound2: "- rep_real (-x) z \<le> B + rep_real x z" for z by (metis abs_le_iff diff_le_eq minus_diff_commute)
  
  show ?thesis
  proof
    assume "sgn x = 1"
    hence asm:"real_positive (rep_real x)" by (simp add: sgn_pos_iff)
    have "\<forall>C\<ge>0. \<exists>N. \<forall>z\<ge>N. rep_real (-x) z \<le> -C"
    proof (clarify)
      fix C assume "0 \<le> (C :: int)"
      with asm B_nonneg obtain N where "\<forall>p\<ge>N. C + B \<le> rep_real x p" by (fastforce elim: boundedE)
      with B_nonneg B_bound1 order.trans have "\<forall>p\<ge>N. C \<le> - rep_real (-x) p" by fastforce
      thus "\<exists>N. \<forall>z\<ge>N. rep_real (-x) z \<le> -C" by force
    qed
    thus "sgn (-x) = -1" by (simp add: sgn_neg_iff)
  next
    assume "sgn (- x) = -1"
    hence asm:"real_negative (rep_real (-x))" by (simp add: sgn_neg_iff)
    have "\<forall>C\<ge>0. \<exists>N. \<forall>z\<ge>N. C \<le> rep_real x z"
    proof (clarify)
      fix C assume "0 \<le> (C :: int)"
      with asm B_nonneg obtain N where "\<forall>p\<ge>N. C + B \<le> -rep_real (-x) p" by (metis real_negative.simps add.inverse_inverse add_nonneg_nonneg neg_le_iff_le)
      with B_nonneg B_bound2 order.trans have "\<forall>p\<ge>N. C \<le> rep_real x p" by fastforce
      thus "\<exists>N. \<forall>z\<ge>N. C \<le> rep_real x z" by force
    qed
    hence "real_positive (rep_real x)" by simp
    thus "sgn x = 1" by (simp add: sgn_pos_iff)
  qed
qed

lemma sgn_range:
  shows "sgn (x :: real) \<in> {-1, 0, 1}"
  unfolding sgn_real_def zero_real_def one_real_def minus_one_real_def by simp

definition
  "x < (y::real) \<equiv> sgn (y - x) = 1"

definition
  "x \<le> (y::real) \<equiv> x < y \<or> x = y"

definition
  abs_real: "\<bar>x :: real\<bar> = (if x < 0 then -x else x)"

instance ..
end

lemmas real_rel_sgn = apply_rsp'[OF sgn_real.rsp, intro]

lemma real_leI:
  assumes "sgn (y - x) \<in> {0 :: real, 1}"
  shows "x \<le> y"
  using assms sgn_zero_iff unfolding less_eq_real_def less_real_def by fastforce

lemma real_lessI:
  assumes "sgn (y - x) = (1 :: real)"
  shows "x < y"
  using assms unfolding less_real_def by blast

instance real :: linorder
proof
  fix x y z :: real
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" by (auto simp: less_eq_real_def less_real_def sgn_zero_iff[THEN iffD2] dest: sgn_uminus[THEN iffD1])
  show "x \<le> x" unfolding less_eq_real_def by blast
  show "\<lbrakk>x \<le> y; y \<le> z\<rbrakk> \<Longrightarrow> x \<le> z" by (auto simp: less_eq_real_def less_real_def) (force dest: sgn_add)
  show "\<lbrakk>x \<le> y; y \<le> x\<rbrakk> \<Longrightarrow> x = y" by (auto simp: less_eq_real_def less_real_def dest: sgn_uminus[THEN iffD1])
  show "x \<le> y \<or> y \<le> x"
  proof (rule disjCI, auto simp: less_eq_real_def less_real_def, goal_cases)
    case 1
    from 1(2) have "x - y \<noteq> 0" by simp
    then have "sgn (x - y) \<noteq> 0" by (rule contrapos_nn) (simp only: sgn_zero_iff[THEN iffD1])
    with 1(1) sgn_range[of "x - y"] show ?case by (auto simp: sgn_uminus)
  qed
qed

instantiation real :: "{inverse}"
begin

fun pos_inverse :: "(int \<Rightarrow> int) \<Rightarrow> (int \<Rightarrow> int)" where
 "pos_inverse f = (\<lambda>z. sgn z * Inf ({0..} \<inter> {n. f n \<ge> \<bar>z\<bar>}))"

fun real_inverse :: "(int \<Rightarrow> int) \<Rightarrow> (int \<Rightarrow> int)" where
  "real_inverse f = real_sgn f o pos_inverse f"

(* TODO *)

lemma pos_inverse_refl: 
  fixes g f
  assumes f_refl: "f \<sim> f"
  shows "pos_inverse f \<sim> pos_inverse f"
  sorry

quotient_definition
  "(inverse :: real \<Rightarrow> real)" is real_inverse
proof (goal_cases)
  case (1 x y)
  then show ?case sorry
qed

definition
  "x div (y::real) \<equiv> inverse y * x"

instance ..
end

lemmas real_rel_inverse = apply_rsp'[OF inverse_real.rsp, intro]

(* TODO *)

lemma real_inverse_uminus:
  assumes "f \<sim> f"
  shows "real_inverse (-f) \<sim> -real_inverse f"
  sorry

lemma real_inverse_abs:
  assumes f_refl: "f \<sim> f" and f_non_zero: "\<not>(f \<sim> (\<lambda>_.0))"
  shows "inverse (abs_real f) * abs_real f = 1" unfolding one_real_def
proof (auto simp del: real_inverse.simps simp add: inverse_real_def,
       subst abs_real_eqI[OF real_rel_inverse, of _ f],
       blast intro: f_refl,
       simp del: real_inverse.simps add: times_real_def,
       rule abs_real_eqI,
       rule real_rel_trans[of _ "real_inverse f o f"], goal_cases)
  case 1
  then show ?case by (metis f_refl inverse_real.rsp real_mult.elims real_rel_mult rel_funD rep_real_inverse)
next
  case 2
  have rel: "real_inverse g \<circ> g \<sim> id " if "g \<sim> g" "\<not>(g \<sim> (\<lambda>_.0))" "real_positive g" for g sorry
  show ?case
  proof (cases "real_positive f")
    case True
    with rel assms show ?thesis by blast 
  next
    case False
    then have pos_neg_f: "real_positive (-f)" using assms sgn_non_zero sgn_uminus_pn by blast
    then have 0: "real_inverse (-f) \<circ> (-f) \<sim> id" by (metis False add.inverse_neutral f_refl non_zero_iff real_uminus_abs(2) rel sgn_neg_iff2 sgn_non_zero sgn_pos_iff2 sgn_uminus)
    then have "abs_real (real_inverse (-f)) * abs_real (-f) = 1" by (metis abs_real_eqI f_refl id_apply one_real_def real_mult.elims real_mult_abs(1) real_rel_inverse real_uminus_abs(2))
    then have "abs_real (real_inverse f) * abs_real f = 1" by (metis abs_real_eqI real_inverse_uminus f_refl minus_mult_minus real_rel_inverse real_uminus_abs(1)) 
    then have "real_inverse f o f \<sim> id" by (metis 0 abs_real_inject f_refl id_apply inverse_real.rsp one_real_def real_mult.elims real_mult_abs(1) real_rel_mult real_rel_reflI'(1) rel_funD)
    with rel assms show ?thesis by blast
  qed
qed


instance real :: field
proof
  fix x y :: real
  show "x \<noteq> 0 \<Longrightarrow> inverse x * x = 1" unfolding inverse_real_def 
    by (metis (no_types, lifting) Quotient3_abs_rep Quotient3_real Quotient_real Quotient_rel_rep inverse_real_def non_zero_iff real_inverse_abs)
  show "x / y = x * inverse y" unfolding divide_real_def by simp
  show "inverse (0 :: real) = 0" unfolding inverse_real_def
    by (simp del: real_sgn.simps, 
        subst real_mult_abs(1)[symmetric, simplified, of "real_sgn (rep_real 0)"],
        force,
        simp only: zero_real_def id_apply,
        rule pos_inverse_refl[of "rep_real (abs_real (\<lambda>_.0))", simplified])
       (fastforce simp: sgn_zero_iff[of 0, unfolded sgn_real_def map_fun_def comp_def, simplified])
qed

instantiation real :: distrib_lattice
begin

definition
  "(inf :: real \<Rightarrow> real \<Rightarrow> real) = min"
                                   
definition
  "(sup :: real \<Rightarrow> real \<Rightarrow> real) = max"

instance
  by standard (auto simp: inf_real_def sup_real_def max_min_distrib2)

end

instance real :: linordered_field
proof
  fix x y z :: real
  show "x \<le> y \<Longrightarrow> z + x \<le> z + y" 
  proof (cases "x = y", auto simp add: less_eq_real_def, induct x, induct y, induct z)
    case (1 h g f)
    from 1(2,3,4) have "real_positive (real_add g (-f))" unfolding less_real_def real_diff_abs[OF 1(2,3), symmetric] by (subst back_subst[of "(\<lambda>x. x)", OF _ sgn_pos_iff2[of "real_add g (- f)"]], auto simp del: real_ring_simps)
    hence "real_positive (\<lambda>z. g z - f z)" by fastforce
    thus ?case using 1(4) less_real_def by force
  qed
  show "\<bar>x\<bar> = (if x < 0 then -x else x)" by (simp only: abs_real)
  show "sgn x = (if x = 0 then 0 else if 0 < x then 1 else - 1)" using sgn_range sgn_zero_iff by (auto simp: less_real_def)
  show "\<lbrakk>x < y; 0 < z\<rbrakk> \<Longrightarrow> z * x < z * y"
  proof (induct x, induct y, induct z)
    case (1 h g f)

    define r where "r = (real_add (real_mult g h) (real_uminus (real_mult f h)))"
    define h0 where "h0 = rep_real (abs_real h)"
    have h0_equiv: "h0 \<sim> h" unfolding h0_def using 1(1) by blast
    
    from 1(2,3,4) have pos_g_f: "real_positive (real_add g (-f))" unfolding less_real_def real_diff_abs[OF 1(2,3), symmetric] by (subst back_subst[of "(\<lambda>x. x)", OF _ sgn_pos_iff2[of "real_add g (- f)"]], auto simp del: real_ring_simps) 
    from 1(5) have pos_h: "real_positive h" unfolding less_real_def using real_diff_abs by (simp add: 1(1) sgn_pos_iff2)

    have "real_positive (real_add (real_mult g h) (real_uminus (real_mult f h)))"
    proof (clarsimp)
      fix D assume "0 \<le> (D :: int)"
      with pos_g_f obtain N where bound1: "\<forall>p\<ge>N. D \<le> g p - f p" by fastforce
      from pos_h obtain N' where bound2: "\<forall>p\<ge>N'. max 0 N \<le> h p" by (metis real_positive.simps max.cobounded1)
      from bound1 bound2 have "\<forall>p\<ge>N'. D \<le> g (h p) - f (h p)" by force
      thus "\<exists>N. \<forall>p\<ge>N. D \<le> g (h p) - f (h p)" by blast
    qed
    then show ?case unfolding less_real_def by (metis 1(1,2,3) mult.commute real_add_abs(2) real_diff_abs real_mult_abs real_uminus.elims real_uminus_abs(2) sgn_pos_iff2)
  qed
qed

instance real :: archimedean_field
proof
  fix x :: real
  show "\<exists>z. x \<le> of_int z"
  proof (induct x)
    case (1 y)
    hence "almost_hom y" using refl_almost_homI by blast
    with almost_hom_linear_bound obtain A B where linear_bound: "\<bar>y z\<bar> \<le> A * \<bar>z\<bar> + B" "0 \<le> A" "0 \<le> B" for z by blast

    have rep_equiv: "rep_real (of_int (A + 1) - abs_real y) \<sim> (real_add ((*) (A + 1)) (- y))" unfolding real_of_int
      real_diff_abs[OF almost_hom_reflI[OF almost_hom_scale[of "A + 1"]] 1, symmetric]
      using 1 almost_hom_reflI almost_hom_scale by blast

    have "\<forall>C \<ge> 0. \<exists>N. \<forall>p \<ge> N. (A + 1) * p - y p \<ge> C"
    proof (clarify)
      fix C assume C_nonneg: "0 \<le> (C :: int)"
      with linear_bound have ineq1: "y z + C \<le> A * \<bar>z\<bar> + B + C" for z using abs_le_D1 by auto
      from C_nonneg linear_bound(2,3) have ineq2: "A * \<bar>z\<bar> + B + C \<le> (A + 1) * \<bar>z\<bar>" if "z \<ge> (B + C)" for z using that by (auto simp: distrib_right)
      have "y z + C \<le> (A + 1) * z" if "z \<ge> (B + C)" for z 
        using order.trans[OF ineq1 ineq2[OF that]] add_nonneg_nonneg[OF C_nonneg linear_bound(3)] abs_of_nonneg[of z] that by linarith
      hence "\<forall>p \<ge> B + C. (A + 1) * p - y p \<ge> C" by fastforce
      thus "\<exists>N. \<forall>p \<ge> N. (A + 1) * p - y p \<ge> C" by blast
    qed

    with rep_equiv[THEN real_rel_sym, THEN pos_invariant]
    have "abs_real y < of_int (A + 1)" unfolding less_real_def sgn_pos_iff by force
    thus ?case unfolding less_eq_real_def by blast
  qed
qed

end