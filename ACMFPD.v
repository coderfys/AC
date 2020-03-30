Require Export Classical.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' 'λ' x .. y ']' , t").

(* 定义初始 " 类 (Class) " ，元素和集合的类型都是 Class *)

Parameter Class : Type.
Parameter element : Class.
Parameter set : Class.
Parameter family : Class.

(* ∈：属于 x∈A : In x A *)

Parameter In : Class -> Class -> Prop.

Notation "x ∈ A" := (In x A) (at level 10).

(* 外延公理I  对于每个A与B,A=B成立之充分必要条件是对每一个x当且仅当x∈A时x∈B *)

Definition Class_Equal (A B: Class) := forall x , x ∈ A <-> x ∈ B.

Axiom Extensionality_Class : forall A B, Class_Equal A B -> A = B.

(* {...:...} *)

Parameter Classifier : forall P: Class -> Prop, Class.

Notation "\{ P \}" := (Classifier P) (at level 0).

Axiom Axiom_Classifier : forall (x: Class) (P: Class -> Prop),
  x ∈ \{ P \} <-> (P x).

(* P是适定的*)

(* 不讨论悖论 *)

Ltac AppC H := apply -> Axiom_Classifier in H; simpl in H.

(* 定义不等于 A≠B 当且仅当 A=B 不真 *)

Definition Inequality (A B: Class) := ~ (A = B).

Notation "A ≠ B" := (Inequality A B) (at level 70).

(* 定义空集 Φ={x:x≠x} *)

Definition Φ : Class := \{λ x, x ≠ x \}.

(* 定义单点集 [x]={z:z=x} *)

Definition Singleton x : Class := \{ λ z,  z=x \}.

Notation "[ x ]" := (Singleton x) (at level 0, right associativity).

(* 定义不属于  x∉A当且仅当x∈A不真 *)

Definition NotIn x A : Prop := ~ x ∈ A.

Notation "x ∉ A" := (NotIn x A) (at level 10).

(* 定义包含  A⊂B 当且仅当对于每个x，如果x∈A，则x∈B *)

Definition Included A B : Prop := forall x, x ∈ A -> x ∈ B.

Notation "A ⊂ B" := (Included A B) (at level 70).

Definition PowerSet X : Class := \{ λ A, A ⊂ X \}.

Notation "CP( X )" := (PowerSet X) (at level 0, right associativity).

Definition Union A B : Class := \{ λ x, x∈A \/ x∈B \}.

Notation "A ∪ B" := (Union A B) (at level 65, right associativity).

(*定义1.2.1 交集 A∩B = {x:x∈A并且x∈B}*)

Definition Intersection A B : Class := \{ λ x, x∈A /\ x∈B \}.

Notation "A ∩ B" := (Intersection A B) (at level 60, right associativity).

Hint Unfold Union Intersection : PointSetTopology.

(*定义1.2.1 无交或者不相交 A ∩ B = Φ *)

Definition NotIntersection A B := A ∩ B = Φ.

(*定义差集 A-B={x:x∈A且x∉B}*)

Definition Setminus A B : Class := \{ λ x, x ∈ A /\ x ∉ B \}.

Notation "A - B" := (Setminus A B) (at level 50, left associativity).

(*为方便集族的交和并运算,引进类的元的交与并运算*)(*CA 即花A*)

(* 定义类的元的交  ∩ CA = {x:对于每个A，如果A∈CA，则x∈A} *) 

Definition Element_I CA : Class := \{ λ x, forall A, A ∈ CA -> x ∈ A \}.

Notation "∩ CA" := (Element_I CA) (at level 66).

Hint Unfold Element_I : PointSetTopology.

(* 定义类的元的并  ∪ CA = {x:对于某个A，x∈A同时A∈CA} *)

Definition Element_U CA : Class := \{ λ x, exists A, x ∈ A /\ A ∈ CA \}.

Notation "∪ CA" := (Element_U CA) (at level 66).

Hint Unfold Element_U : PointSetTopology.

(* 定义 1.3.2 无序偶 *)

Definition Unordered x y : Class := [x]∪[y].

Notation "[ x | y ]" := (Unordered x y) (at level 0).

Hint Unfold Unordered : PointSetTopology.

(* 定义 1.3.2 有序偶 *)

Definition Ordered x y : Class := [ [x] | [x|y]].

Notation "[ x , y ]" := (Ordered x y) (at level 0).

Hint Unfold Ordered : PointSetTopology.

(* 定义 1.3.1 笛卡尔积 *)

Parameter Classifier_P : (Class -> Class -> Prop) -> Class.

Notation "\{\ P \}\" := (Classifier_P P) (at level 0).

Axiom Axiom_Classifier' : forall x y P, [x,y] ∈ \{\ P \}\ <->  P x y.

Axiom Property_P : forall z P,
  z ∈ \{\ P \}\ -> (exists x y, z = [x,y]) /\ z ∈ \{\ P \}\.

Ltac PP H := apply Property_P in H; destruct H as [[a [b H]]]; rewrite H in *.

Ltac AppC' H := apply -> Axiom_Classifier' in H; simpl in H.

Hint Resolve Axiom_Classifier' Property_P : PointSetTopology.

(* 定义 X × Y={[x,y]:x∈X/\y∈Y} *)

Definition Cartesian X Y : Class := \{\ λ x y, x∈X /\ y∈Y \}\.

Notation "X × Y" := (Cartesian X Y)(at level 2, right associativity).

(* 定义1.3.3 关系  R ⊂ X × Y *)

Definition Relation R X Y : Prop := R ⊂ X × Y.

(* 定义1.3.4 R相关的, 象集, 值域 *)

Definition Rrelation x R y : Prop := [x,y] ∈ R.

Definition Image R A := \{ λ y, exists x, x∈ A /\ [x,y] ∈ R \}.

Notation " R [ A ]I " := (Image R A)(at level 5).

Definition Range R := \{ λ y, exists x, [x,y] ∈ R \}.

Notation "ran( R )" := (Range R )(at level 5).

(* 1.3.5 定义R的逆，原象，定义域 *)

Definition Inverse R : Class := \{\ λ x y, [y,x]∈R \}\.

Notation "R ⁻¹" := (Inverse R)(at level 0).

Definition OriginalImage R B := \{ λ x, exists y, y∈ B /\[y,x] ∈ R⁻¹ \}.

Definition Domain R := \{ λ x, exists y, [x,y] ∈ R \}.

Notation "dom( R )" := (Domain R)(at level 5).

(*定义1.4.1 恒同关系*)

Definition InRelation R X := R ⊂ X × X.

Definition IdenRelation X := \{\ λ x y, x ∈ X /\ y ∈ X /\ x = y\}\.

Notation "∆ [ X ] " := (IdenRelation X)(at level 5).

(*定义 1.4.2 自反，对称，反对称，传递*)

Definition Reflexive R X := R ⊂ X × X /\ (forall x, x ∈ X -> [x,x]∈R).

Definition Symmetric R X := forall x y, (x ∈ X /\ y ∈ X 
  /\ [x,y]∈R) -> [y,x]∈R.

Definition Asymmetric R X := forall x y, x ∈ X /\ y ∈ X 
  /\ ~ ([x,y]∈R /\ [y,x]∈R).

Definition Transitive R X := forall x y z, (x∈X /\ y∈X 
  /\ z∈X /\ [x,y]∈R /\ [y,z]∈R) -> [x,z]∈R.

(*Definition Asymmetric' R X := forall x y, (x ∈ X /\ y ∈ X /\[x,y]∈R) -> ~ [y,x]∈R.*)

(*定义 等价关系*)

Definition EqualRelation R X := Reflexive R X /\ Symmetric R X /\ Transitive R X.

Definition EqualRelation1 X := \{\ λ A B, A ∈ (PowerSet X) /\ B ∈ (PowerSet X)
   /\ A = B \}\.

Notation "∆1 [ X ] " := (EqualRelation1 X)(at level 5).

(*定义1.5.1 映射*)

Definition Function F X Y : Prop :=
  Relation F X Y /\ (forall x, x ∈ X -> exists y, [x,y] ∈ F)
  /\ (forall x y z, [x,y] ∈ F /\ [x,z] ∈ F -> y=z).

(*定义1.5.2 值 原象*)

Definition Value F x := ∩ \{ λ y, [x,y] ∈ F \}. 

Notation "F [ x ]" := (Value F x)(at level 5).

(* 定义1.5.3 满射，单射，一一映射 *) 

Definition FullF' f X Y :=f[X]I = Y.

Definition FullF f X Y := 
  Function f X Y /\ FullF' f X Y.
  
Definition Singlef' f X := forall x1 x2, 
  x1 ∈ X -> x2 ∈ X -> x1 <> x2 -> f[x1] <> f[x2].
  
Definition Singlef f X Y := Function f X Y /\ Singlef' f X.

Definition One_to_onef f X Y := Function f X Y /\ FullF' f X Y /\ Singlef' f X.
  
Definition ConstantF f X Y := Function f X Y /\ exists y, f[X]I = [y].

Definition IdFunction X := ∆ [ X ].

Definition UnitFunction  X := IdFunction  X.

Notation "id[ X ] " := (IdFunction X)(at level 5).

(* 有标集族 *)

Definition MarkFamilySet φ Γ CA (l:FullF φ Γ CA ) := \{\ λ γ y, γ∈Γ /\ y = φ[γ] \}\.

(* 定义1.6.1 集族的并，交   *)

Definition Un_FamilySet' φ Γ CA (l:FullF φ Γ CA ) := 
   \{ λ x, exists γ, γ∈Γ /\ x∈φ[γ] \}.

Definition In_FamilySet' φ Γ CA (l:FullF φ Γ CA ) := 
   \{ λ x, forall γ, γ∈Γ -> x∈φ[γ] \}.

Definition UsFamily φ Γ CA (l:FullF φ Γ CA ) :=
  \{ λ x, exists γ, γ∈Γ /\ x = φ[γ] \}.
  
(*定义1.8.1 选择函数*)

Definition SubFamily X := CP(X) - [Φ].

Notation "  X ^ " := (SubFamily X) (at level 0).

Definition ChoiceFunction ε X := Function ε X^ X /\ (forall A,A∈X^ -> ε[A]∈A).

(*选择公理1.8.1*)

Axiom ChoiceAxiom : forall X, exists ε, ChoiceFunction ε X.

(* 集族的笛卡尔积 *)

Definition FamilyCartesian X Γ CX l :=
  \{λ x, Function x Γ (Un_FamilySet' X Γ CX l) 
  /\ forall γ, γ∈Γ -> x[γ] ∈ X[γ] \}.

(* 第γ个坐标 *)
Definition FamilyCoordinates x γ X Γ CX l :=
  ∩ \{λ y, x ∈ (FamilyCartesian X Γ CX l) /\ y = x[γ]\}. 
(* 第γ个坐标集 *)
Definition FamilyProject α X Γ CX l :=
  \{\λ x y, x ∈ (FamilyCartesian X Γ CX l) 
  /\  y = (FamilyCoordinates x α X Γ CX l)\}\.
 
Lemma Property_Value : forall x f X Y, Function f X Y -> x ∈ X -> [x,f[x]] ∈ f.
Proof.
  intros. destruct H, H1. apply H1 in H0. destruct H0.
  assert (x0=f[x]).
  { apply Extensionality_Class; split; intros.
    + apply Axiom_Classifier; intros. AppC H4.
      assert (A = x0).
      { eapply H2; eauto. }
      rewrite H5; auto.
    + AppC H3. apply H3. apply Axiom_Classifier; auto. }
  rewrite <- H3; auto.
Qed.
  
Lemma Lemma1sss :  Φ^ = Φ.
Proof.
 apply Extensionality_Class; red; split; intros.
 - AppC H; destruct H; AppC H.
   assert (x<>Φ).
   { intro; elim H0; rewrite H1; apply Axiom_Classifier; auto. }
   elim H1; apply Extensionality_Class; red; split; intros.
   + auto.
   + AppC H2; elim H2; auto.
 - AppC H; elim H; auto.  
Qed.

Definition ε1 ε Γ φ := \{\λ x y, x ∈Γ /\ y = ε[φ[x]] \}\.

Theorem Theorem1_9_1 : forall φ Γ CX l, FamilyCartesian φ Γ CX l ≠ Φ
  <-> forall γ, γ∈Γ -> φ[γ]≠ Φ.
Proof.
 split; intros.
 - assert (Γ ≠ Φ).
   { intro. rewrite H1 in H0. AppC H0. auto. }
   intro. elim H. apply Extensionality_Class; red; split; intros.
    + AppC H3; destruct H3. apply H4 in H0. rewrite H2 in H0. AppC H0.
      elim H0. auto.
    + AppC H3. elim H3; auto. 
 - intro. 
    generalize (ChoiceAxiom (Un_FamilySet' φ Γ CX (l:FullF φ Γ CX ) )).
    intros; destruct H1. red in H1. destruct H1.
    assert ((ε1 x Γ φ) ∈ (FamilyCartesian φ Γ CX l)).
    { assert (Function (ε1 x Γ φ) Γ (Un_FamilySet' φ Γ CX l)).
      { repeat split.
        - red; red; intros.
        PP H3. AppC' H4; destruct H4.
        red in H1; destruct H1, H6.
        apply Axiom_Classifier'. split; auto.
        apply Axiom_Classifier.
        rewrite H5. exists a; split; auto.
        apply H2. 
        apply Axiom_Classifier. split.
        + apply Axiom_Classifier. red; intros.
          apply Axiom_Classifier. exists a; auto.
        + intro. AppC H8. apply H in H4. contradiction.
      - intros. exists x[φ[x0]]. apply Axiom_Classifier'. split; auto.
      - intros; destruct H3. AppC' H3; destruct H3. AppC' H4; destruct H4.
        rewrite H5; auto. }
      apply Axiom_Classifier. split; auto. 
      intros. eapply Property_Value in H3; eauto.
      AppC' H3; destruct H3.
      rewrite H5. 
      apply H2. 
      apply Axiom_Classifier. split.
      + apply Axiom_Classifier. red; intros.
        apply Axiom_Classifier. exists γ; auto.
      + intro. AppC H6. apply H in H4. contradiction. }
      rewrite H0 in H3. AppC H3; auto.
Qed.

Lemma lemma1_5_3a: forall f X, f = ∆ [ X ] -> Function f X X.
Proof.
  intros.
  red. repeat split; intros.
  - red. red. intros. unfold IdenRelation in H0. rewrite H in H0. PP H0. AppC' H1.
    apply Axiom_Classifier'. split; tauto.
  - exists x. rewrite H. apply Axiom_Classifier'. split; tauto.
  - rewrite H in H0. destruct H0.
    AppC' H0. AppC' H1. destruct H0, H2. rewrite <- H3. tauto.
Qed.

Lemma lemma1_5_3b: forall f X, f = ∆ [ X ]-> One_to_onef f X X.
Proof.
  intros. rewrite H in *.
  red; repeat split; intros. 
  - rewrite <- H. apply lemma1_5_3a; auto.
  - exists x. apply Axiom_Classifier'. split; auto.
  - destruct H0. AppC' H0. AppC' H1.
    destruct H0, H2. rewrite <- H3; tauto.
  - red. apply Extensionality_Class; red; split; intros.  
    + AppC H0; destruct H0, H0. AppC' H1; destruct H1, H2; auto.
    + apply Axiom_Classifier. exists x. split; auto.
      apply Axiom_Classifier'. repeat split; auto.
  - red. intros. intro.
    assert (forall x, x ∈ X -> ∆ [X][x]= x).
    { intros. apply Extensionality_Class; red; split; intros.
      + AppC H5. apply H5. apply Axiom_Classifier. 
        apply Axiom_Classifier'. split; auto.
      + apply Axiom_Classifier. intros. AppC H6. AppC' H6. 
        destruct H6, H7. rewrite <- H8; auto. }
        rewrite H4 in H3; auto. rewrite H4 in H3; auto.
Qed.

Lemma Lemma11 : forall A,  ~ (exists B, B ∈ A) -> forall B, B ∉ A.
Proof.
  intros; intro; elim H; exists B; auto.
Qed.  

Lemma Lemma12 : forall A,  A ≠ Φ -> exists B, B ∈ A.
Proof.
  intros.
  generalize (classic ( exists B : Class, B ∈ A)).
  intros. destruct H0.
  - auto.
  - elim H. apply Extensionality_Class; red; split; intros.
    + apply Lemma11 in H1; auto. contradiction.
    + AppC H1; elim H1; auto.
Qed.

Lemma lemma1_9_11 : forall x X, x ∈ X -> x = (∆[X])[x].
Proof.
  intros; apply Extensionality_Class; split; intros.
  - apply Axiom_Classifier; intros.
    AppC H1. AppC' H1. destruct H1, H2. rewrite <- H3; auto.
  - AppC H0. apply H0. apply Axiom_Classifier. apply Axiom_Classifier'; tauto. 
Qed.

Theorem Theorem1_9_11 : forall X, exists ε, ChoiceFunction ε X.
Proof.
  intros.
  generalize (classic (X=Φ)); intros; destruct H.
  - exists \{\λ x y, x ∈Φ /\ y ∈Φ \}\; red; repeat split.
    + red; red; intros; PP H0; AppC' H1; destruct H1.
      AppC H1; elim H1; auto.
    + intros; rewrite H in H0; rewrite Lemma1sss in H0.
      AppC H0; elim H0; auto.
    + intros; destruct H0; AppC' H0; destruct H0.
      AppC H0; elim H0; auto. 
    + intros; rewrite H in H0;rewrite Lemma1sss in H0.
      AppC H0; elim H0; auto.
  - assert (X^<> Φ).
    { assert (∪X^ = X).
      { apply Extensionality_Class; split; intros.
        - AppC H0; destruct H0, H0. AppC H1; destruct H1. 
          AppC H1; auto.
        - apply Axiom_Classifier. exists [x]; split.
          + apply Axiom_Classifier; auto.
          + apply Axiom_Classifier; split.
            * apply Axiom_Classifier; red; intros.
              AppC H1; rewrite H1; auto.
            * intro. AppC H1. 
              assert (x ∈ [x]).
              { apply Axiom_Classifier; auto. }
              rewrite H1 in H2. AppC H2; elim H2; auto. }
  intro.
  assert (∪(X^) = Φ).
  { rewrite H1. apply Extensionality_Class; split; intros.
    - AppC H2; destruct H2, H2. AppC H3; elim H3; auto.
    - AppC H2; elim H2; auto. }
  apply H. rewrite <- H0; auto. }
  generalize (Theorem1_9_1); intros.
  assert (FullF ∆[X^] X^ X^).
  { generalize (lemma1_5_3b ∆[X^] X^); intros.
    destruct H2; auto. destruct H3; red; auto. }
  pose proof (H1 ∆[X^] X^ X^ H2).
  assert (forall γ, γ ∈ X^ -> (∆[X^])[γ] ≠ Φ); intros.
  { AppC H4; destruct H4; AppC H4; intro.
    apply H5; apply Axiom_Classifier; rewrite <- H6.
    apply Extensionality_Class; split; intros.
    - apply Axiom_Classifier; intros. AppC H8; AppC' H8.
      destruct H8 as [_ [_ H8]]; rewrite H8 in H7; auto.
    - AppC H7; apply H7; apply Axiom_Classifier.
      apply Axiom_Classifier'; repeat split; auto;
      apply Axiom_Classifier; split; auto;
      apply Axiom_Classifier; auto. }
  apply H3 in H4; apply Lemma12 in H4.
  destruct H4 as [ε H4]; AppC H4; destruct H4.
  exists ε; split; intros.
  + assert ((Un_FamilySet' ∆[X^] X^ X^ H2) = X).
    { apply Extensionality_Class; split; intros.
      - AppC H6; destruct H6, H6; AppC H6; destruct H6.
        AppC H6; rewrite <- lemma1_9_11 in H7. 
        apply H6 in H7; auto.
        apply Axiom_Classifier; split; auto.
        apply Axiom_Classifier; auto.
      - apply Axiom_Classifier; exists [x]; split.
        + apply Axiom_Classifier; split.
          * apply Axiom_Classifier; red; intros.
            AppC H7; rewrite H7; auto.
          * intro; AppC H7. 
            assert (x ∈ [x]).
            { apply Axiom_Classifier; auto. }
            rewrite H7 in H8. AppC H8; elim H8; auto.
        + apply Axiom_Classifier; intros.
          AppC H7. AppC' H7. destruct H7, H8.
          rewrite <- H9. apply Axiom_Classifier; auto. }
  rewrite  H6 in H4; auto.
  + pose proof H6. apply H5 in H6.
    rewrite <- lemma1_9_11 in H6; auto.
Qed.
