Require Import Utf8.

Definition inc : Set → Set := option.

Definition ext {V : Set} {U} (γ : V → U) (u : U) : inc V → U :=
  fun o => match o with
  | None => u
  | Some v => γ v
  end.


Inductive exp (V : Set) : Set :=
| e_val : val V → exp V
| e_app : exp V → exp V → exp V
| e_do : val V → exp V
| e_lift : exp V → exp V
| e_hndl : exp V → exp (inc (inc V)) → exp (inc V) → exp V
with val (V : Set) : Set :=
| v_var : V → val V
| v_lam : exp (inc V) → val V
.



Arguments e_val [V] _.
Arguments e_app [V] _ _.
Arguments e_do [V] _.
Arguments e_lift [V] _.
Arguments e_hndl [V] _ _ _.
Arguments v_var {V} _.
Arguments v_lam [V] _.

Inductive ktx (V : Set) : Set :=
| k_hole : ktx V
| k_fun : ktx V → exp V → ktx V
| k_arg : val V → ktx V → ktx V
| k_lift : ktx V → ktx V
| k_hndl : ktx V → exp (inc (inc V)) → exp (inc V) → ktx V
.

Arguments k_hole {V}.
Arguments k_fun [V] _ _.
Arguments k_arg [V] _ _.
Arguments k_lift [V] _.
Arguments k_hndl [V] _ _ _.

Inductive free {V : Set} : nat → ktx V → Set :=
| f_hole : free O (k_hole)
| f_fun : ∀ K n, free n K → ∀ (e : exp V), free n (k_fun K e)
| f_arg : ∀ K n, free n K → ∀ (v : val V), free n (k_arg v K)
| f_lift : ∀ K n, free n K → free (S n) (k_lift K)
| f_hndl : ∀ K n, free (S n) K → ∀ (eh : exp (inc (inc V))) (er : exp (inc V)),
    free n (k_hndl K eh er)
.

Fixpoint plug {V} (K : ktx V) (e : exp V) : exp V :=
  match K with
  | k_hole => e
  | k_fun K' x => e_app (plug K' e) x
  | k_arg f K' => e_app (e_val f) (plug K' e)
  | k_lift K' => e_lift (plug K' e)
  | k_hndl K' eh er => e_hndl (plug K' e) eh er
  end
.

Definition exp0 := exp Empty_set.
Definition exp1 := exp (inc Empty_set).
Definition exp2 := exp (inc (inc Empty_set)).

Definition val0 := val Empty_set.
Definition val1 := val (inc Empty_set).
Definition val2 := val (inc (inc Empty_set)).

Definition ktx0 := ktx Empty_set.
Definition ktx1 := ktx (inc Empty_set).
Definition ktx2 := ktx (inc (inc Empty_set)).

Definition liftren {V U : Set} (ρ : V → U) : inc V → inc U := option_map ρ.

Fixpoint map_exp {V U : Set} (ρ : V → U) (e : exp V) : exp U :=
  match e with
  | e_val v => e_val (map_val ρ v)
  | e_app e1 e2 => e_app (map_exp ρ e1) (map_exp ρ e2)
  | e_do v => e_do (map_val ρ v)
  | e_lift e => e_lift (map_exp ρ e)
  | e_hndl e eh er => e_hndl (map_exp ρ e) (map_exp (liftren (liftren ρ)) eh) (map_exp (liftren ρ) er)
  end
with map_val {V U : Set} (ρ : V → U) (v : val V) : val U :=
  match v with
  | v_var v => v_var (ρ v)
  | v_lam e => v_lam (map_exp (liftren ρ) e)
  end.

Fixpoint map_ktx {V U : Set} (ρ : V → U) (K : ktx V) : ktx U :=
  match K with
  | k_hole => k_hole
  | k_fun K' e => k_fun (map_ktx ρ K') (map_exp ρ e)
  | k_arg v K' => k_arg (map_val ρ v) (map_ktx ρ K')
  | k_lift K' => k_lift (map_ktx ρ K')
  | k_hndl K' eh er => k_hndl (map_ktx ρ K') (map_exp (liftren (liftren ρ)) eh) (map_exp (liftren ρ) er)
  end.

Definition weaken_exp {V : Set} (e : exp V) : exp (inc V) := map_exp Some e.
Definition weaken_val {V : Set} (e : val V) : val (inc V) := map_val Some e.
Definition weaken_ktx {V : Set} (e : ktx V) : ktx (inc V) := map_ktx Some e.

Definition liftsub {V U : Set} (γ : V → val U) : inc V → val (inc U) :=
  fun o => match o with
  | None => v_var None
  | Some v => map_val Some (γ v)
  end.


Fixpoint bind_exp {V U : Set} (γ : V → val U) (e : exp V) : exp U :=
  match e with
  | e_val v => e_val (bind_val γ v)
  | e_app e1 e2 => e_app (bind_exp γ e1) (bind_exp γ e2)
  | e_do v => e_do (bind_val γ v)
  | e_lift e => e_lift (bind_exp γ e)
  | e_hndl e eh er => e_hndl (bind_exp γ e) (bind_exp (liftsub (liftsub γ)) eh) (bind_exp (liftsub γ) er)
  end
with bind_val {V U : Set} (γ : V → val U) (v : val V) : val U :=
  match v with
  | v_var v => γ v
  | v_lam e => v_lam (bind_exp (liftsub γ) e)
  end.


Definition sub1 {V} (s : val V) (b : exp (inc V)) :=
  bind_exp (ext v_var s) b.
Definition sub2 {V} (s1 : val V) (s2 : val V) (b : exp (inc (inc V))) :=
  bind_exp (ext (ext v_var s1) s2) b.

Require Import Program.Basics.

Lemma liftsub_compose
  : ∀ {V U W : Set} (f : U → val W) (g : V → U)
  , ∀ v, liftsub (compose f g) v = compose (liftsub f) (liftren g) v.
Proof.
  intros.
  induction v; auto.
Qed.


Lemma liftsub_cong
  : ∀ {V U : Set} (f1 f2 : V → val U) v, (∀ v, f1 v = f2 v)
  → liftsub f1 v = liftsub f2 v.
Proof.
  intros.
  destruct v; simpl; auto. rewrite H. auto.
Qed.


Lemma bind_cong_exp
  : ∀ {V U : Set} (f1 f2 : V → val U) e (ext : ∀ v, f1 v = f2 v)
  , bind_exp f1 e = bind_exp f2 e
with bind_cong_val
  : ∀ {V U : Set} (f1 f2 : V → val U) v (ext : ∀ v, f1 v = f2 v)
  , bind_val f1 v = bind_val f2 v.
Proof.
  - intros.
    destruct e;
    simpl;
    f_equal;
    try (apply bind_cong_exp || apply bind_cong_val);
    intros;
    try (apply liftsub_cong; intros);
    try (apply liftsub_cong; intros);
    apply ext0.
  - intros.
    destruct v;
    simpl;
    f_equal.
    apply bind_cong_exp.
    intro. apply liftsub_cong.
    exact ext0.
Qed.


Lemma bind_map_val
  : ∀ {V U W : Set} (f : U → val W) (g : V → U) (v : val V)
  , bind_val f (map_val g v) = bind_val (compose f g) v
with bind_map_exp
  : ∀ {V U W : Set} (f : U → val W) (g : V → U) (e : exp V)
  , bind_exp f (map_exp g e) = bind_exp (compose f g) e.
Proof.
  - intros.
    destruct v; simpl; auto.
    apply f_equal.
    rewrite bind_map_exp.
    eapply bind_cong_exp; intro.
    symmetry.
    apply liftsub_compose.
  - intros.
    destruct e; simpl; f_equal;
    try (apply bind_map_val || apply bind_map_exp).
    + transitivity (bind_exp (compose (liftsub (liftsub f)) (liftren (liftren g))) e2).
      rewrite bind_map_exp. trivial.
      apply bind_cong_exp; intro.
      symmetry.
      transitivity (liftsub (compose (liftsub f) (liftren g)) v).
      apply liftsub_cong; intro.
      apply liftsub_compose.
      apply liftsub_compose.
    + rewrite bind_map_exp.
      apply bind_cong_exp; intro.
      symmetry. apply liftsub_compose.
Qed.

Lemma liftsub_pure
  : ∀ {V} (v : inc V), liftsub v_var v = v_var v.
Proof.
  intros.
  induction v; auto.
Qed.


Lemma bind_pure_exp
  : ∀ {V} (e : exp V), bind_exp v_var e = e
with bind_pure_val
  : ∀ {V} (v : val V), bind_val v_var v = v.
Proof.
  all: intros.
  + destruct e; simpl; f_equal;
    try apply bind_pure_exp || apply bind_pure_val;
    rewrite <- (bind_cong_exp v_var).
    apply bind_pure_exp.
    intro.
    rewrite (liftsub_cong (liftsub v_var) v_var).
    rewrite liftsub_pure; trivial.
    intro. apply liftsub_pure.
    apply bind_pure_exp.
    intro. rewrite liftsub_pure; trivial.
  + destruct v.
    simpl.
    f_equal.
    simpl.
    f_equal.
    rewrite <- (bind_cong_exp v_var).
    apply bind_pure_exp.
    intro.
    rewrite liftsub_pure. trivial.
Qed.

Lemma sub1_weaken
  : ∀ {V} (K : ktx V) (v : val V)
  , sub1 v (plug (weaken_ktx K) (e_val (v_var None)))
  = plug K (e_val v).
Proof.
  intros.
  induction K; cbn; f_equal; try apply IHK; try f_equal;
  rewrite bind_map_exp || rewrite bind_map_val.
  all: try rewrite <- liftsub_compose.
  apply bind_pure_exp.
  apply bind_pure_val.
  all: rewrite <- (bind_cong_exp v_var).
  apply bind_pure_exp.
  intro. rewrite <- liftsub_compose.
  rewrite (liftsub_cong _ v_var).
  rewrite liftsub_pure; trivial.
  intro.
  rewrite <- liftsub_compose.
  rewrite (liftsub_cong _ v_var).
  apply liftsub_pure.
  intro.
  trivial.
  apply bind_pure_exp.
  intro.
  rewrite <- liftsub_compose.
  rewrite (liftsub_cong _ v_var).
  rewrite liftsub_pure; trivial.
  intro.
  trivial.
Qed.

Lemma liftren_cong
  : ∀ {V U : Set} (f1 f2 : V → U) v, (∀ v, f1 v = f2 v)
  → liftren f1 v = liftren f2 v.
Proof.
  intros.
  destruct v; simpl; f_equal; trivial.
Qed.

Lemma map_cong_exp
  : ∀ {V U : Set} (f1 f2 : V → U) e (ext : ∀ v, f1 v = f2 v)
  , map_exp f1 e = map_exp f2 e
with map_cong_val
  : ∀ {V U : Set} (f1 f2 : V → U) v (ext : ∀ v, f1 v = f2 v)
  , map_val f1 v = map_val f2 v.
Proof.
  - intros.
    destruct e; simpl; f_equal;
    try (apply map_cong_exp || apply map_cong_val); try exact ext0.
    + intros.
      apply liftren_cong; intro.
      apply liftren_cong; intro.
      apply ext0.
    + intro.
      apply liftren_cong; intro.
      apply ext0.
  - intros.
    destruct v; simpl; f_equal.
    + apply ext0.
    + apply map_cong_exp.
      intro.
      apply liftren_cong; intro.
      apply ext0.
Qed.

Lemma liftren_compose
  : ∀ {V U W : Set} (f : U → W) (g : V → U)
  , ∀ v, liftren (compose f g) v = compose (liftren f) (liftren g) v.
Proof.
  intros.
  induction v; auto.
Qed.

Lemma map_compose_exp
  : ∀ {V U W : Set} (f : U → W) (g : V → U)
  , ∀ e, map_exp (compose f g) e = map_exp f (map_exp g e)
with map_compose_val
  : ∀ {V U W : Set} (f : U → W) (g : V → U)
  , ∀ v, map_val (compose f g) v = map_val f (map_val g v).
Proof.
  - destruct e; simpl; f_equal;
    try (apply map_compose_exp || apply map_compose_val).
    + erewrite <- map_compose_exp.
      apply map_cong_exp; intro.
      rewrite <- liftren_compose.
      apply liftren_cong; intro.
      apply liftren_compose.
    + rewrite <- map_compose_exp.
      apply map_cong_exp; intro.
      apply liftren_compose.
  - destruct v; simpl; f_equal.
    rewrite <- map_compose_exp.
    apply map_cong_exp; intro.
    apply liftren_compose.
Qed.

Lemma liftsub_compose2
  : ∀ {V U W : Set} (f : U → W) (g : V → val U)
  , ∀ v, liftsub (compose (map_val f) g) v = compose (map_val (liftren f)) (liftsub g) v.
Proof.
  intros.
  induction v; auto. cbn.
  unfold compose.
  rewrite <- map_compose_val.
  rewrite <- map_compose_val.
  trivial.
Qed.



Lemma map_bind_val
  : ∀ {V U W : Set} (f : U → W) (g : V → val U) (v : val V)
  , map_val f (bind_val g v) = bind_val (compose (map_val f) g) v
with map_bind_exp
  : ∀ {V U W : Set} (f : U → W) (g : V → val U) (e : exp V)
  , map_exp f (bind_exp g e) = bind_exp (compose (map_val f) g) e.
Proof.
  - destruct v; simpl; f_equal.
    + trivial.
    + simpl. f_equal.
      symmetry.
      erewrite bind_cong_exp.
      symmetry. apply map_bind_exp.
      intro.
      apply liftsub_compose2.
  - destruct e; simpl; f_equal.
    all: try (apply map_bind_val || apply map_bind_exp).
    + symmetry; erewrite bind_cong_exp.
      symmetry. apply map_bind_exp.
      intro.
      rewrite <- liftsub_compose2.
      apply liftsub_cong; intro.
      rewrite <- liftsub_compose2.
      apply liftsub_cong; intro. trivial.
    + rewrite map_bind_exp.
      apply bind_cong_exp; intro.
      rewrite <- liftsub_compose2. trivial.
Qed.


Lemma liftsub_compose_bind
  : ∀ {V U W : Set} (f : U → val W) (g : V → val U)
  , ∀ v, liftsub (compose (bind_val f) g) v = bind_val (liftsub f) (liftsub g v).
Proof.
  intros.
  destruct v.
  - simpl. rewrite bind_map_val.
    unfold compose.
    rewrite map_bind_val.
    apply bind_cong_val; intro. trivial.
  - simpl. trivial.
Qed.

Lemma bind_compose_exp
  : ∀ {V U W : Set} (f : U → val W) (g : V → val U)
  , ∀ e, bind_exp (compose (bind_val f) g) e = bind_exp f (bind_exp g e)
with bind_compose_val
  : ∀ {V U W : Set} (f : U → val W) (g : V → val U)
  , ∀ v, bind_val (compose (bind_val f) g) v = bind_val f (bind_val g v).
Proof.
  - intros.
    destruct e; simpl; f_equal.
    all: try (apply bind_compose_exp || apply bind_compose_val).
    + rewrite <- bind_compose_exp.
      apply bind_cong_exp; intro.
      unfold compose.
      erewrite <- liftsub_compose_bind.
      apply liftsub_cong; intro.
      apply liftsub_compose_bind.
    + rewrite <- bind_compose_exp.
      apply bind_cong_exp; intro.
      unfold compose.
      apply liftsub_compose_bind.
  - destruct v; simpl; f_equal.
    trivial.
    rewrite <- bind_compose_exp.
    apply bind_cong_exp; intro.
    apply liftsub_compose_bind.
Qed.
