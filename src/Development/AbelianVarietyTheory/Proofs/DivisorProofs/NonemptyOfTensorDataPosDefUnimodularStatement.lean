module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgIdemBinv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeStepGeneratorTensorPowerPairs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoGluedFromLinCombPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinCombPullbackTransportIsoWithValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoCompLinCombGenerator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamPtsPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaValueProductFormulaDegeneration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosVec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStronglyTrivialCubicalThetaFinsuppTensor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedGeneratorUniqueGlobalFunctionsBase
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjMumfordTensorPowerOfPosDef
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TauBalPow
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteNormalising
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataMatrixActionRingHomProperties
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordIsoPeriodsFactorTensorPolarised, Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordIsoPeriodsFactorTensorPolarisedStatement, Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTrivialMumfordFormalSumLatticeAdditivityRelati, Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPeriodsBalancedIntegralMatrices, Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPeriodsBalancedIntegralMatricesStatement, Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyOfTensorDataPosDefUnimodular, Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyOfTensorDataPosDefUnimodularStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordIsoPeriodsFactorTensorPolarised =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordIsoPeriodsFactorTensorPolarised", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgIdemBinv\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeStepGeneratorTensorPowerPairs\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoGluedFromLinCombPullback\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinCombPullbackTransportIsoWithValues\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoCompLinCombGenerator\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamPtsPull\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaValueProductFormulaDegeneration\nimport Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TauBalPow\nimport Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteNormalising\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull\nimport Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum.PolPair

section Has

variable {X Y Z : Scheme.{0}} (L : LB X) {N : Type} (r : N → (Z ⟶ Y))

def Has (F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U)
    (v : N → ∀ z : Z, ((Z ⟶ X) → L.ι) → (Z.presheaf.stalk z)ˣ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = F U h) ∧
    ∀ i z J, Good L z J → val t (r i) z J = v i z J

variable {L r}

theorem Has.congr {F F' v v'} (h : Has L r F v) (hF : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), F U h = F' U h)
    (hv : ∀ i z J, Good L z J → v i z J = v' i z J) : Has L r F' v' := by
  obtain ⟨K, _, φ, ε, t, ht, hf, hw⟩ := h
  exact ⟨K, _, φ, ε, t, ht, fun U _ h => (hf U h).trans (hF U h), fun i z J hJ => (hw i z J hJ).trans (hv i z J hJ)⟩

theorem Has.one : Has L r (fun _ _ _ => 1) (fun _ _ _ => 1) :=
  ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, LB.oneGen L,
    fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm,
    fun U _ h => Fintype.prod_empty _, fun i z J _ => val_one _⟩

theorem Has.mul {F F' v v'} (h : Has L r F v) (h' : Has L r F' v') :
    Has L r (fun U _ g => F U g * F' U g) (fun i z J => v i z J * v' i z J) := by
  obtain ⟨K, _, φ, ε, t, ht, hf, hw⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', hf', hw'⟩ := h'
  refine ⟨K ⊕ K', inferInstance, Sum.elim φ φ', Sum.elim ε ε', LB.mulGen L _ _ _ _ t t',
    DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht', fun U _ h => ?_, fun i z J hJ => ?_⟩
  · beta_reduce; rw [Fintype.prod_sum_type, ← hf, ← hf']; rfl
  · rw [val_mul hJ, hw i z J hJ, hw' i z J hJ]

theorem Has.inv {F v} (h : Has L r F v) : Has L r (fun U _ g => (F U g)⁻¹) (fun i z J => (v i z J)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, hf, hw⟩ := h
  refine ⟨K, inferInstance, φ, _, LB.invGen L _ _ t, DVR.invGen_isGen _ _ _ _ ht, fun U _ h => ?_, fun i z J hJ => ?_⟩
  · beta_reduce; rw [← hf]; simp only [zpow_neg, Finset.prod_inv_distrib]
  · rw [val_inv, hw i z J hJ]

theorem Has.zpow {F v} (h : Has L r F v) (n : ℤ) :
    Has L r (fun U _ g => F U g ^ n) (fun i z J => v i z J ^ n) := by
  induction n using Int.induction_on with
  | zero => exact Has.one.congr (fun _ _ _ => (zpow_zero _).symm) (fun _ _ _ _ => (zpow_zero _).symm)
  | succ n ih => exact (ih.mul h).congr (fun _ _ _ => (zpow_add_one _ _).symm) (fun _ _ _ _ => (zpow_add_one _ _).symm)
  | pred n ih =>
    exact (ih.mul h.inv).congr (fun _ _ _ => (zpow_sub_one _ _).symm) (fun _ _ _ _ => (zpow_sub_one _ _).symm)

theorem Has.prod {κ : Type} {F : κ → _} {v : κ → _} (h : ∀ j, Has L r (F j) (v j)) (s : Finset κ) :
    Has L r (fun U _ g => ∏ j ∈ s, F j U g) (fun i z J => ∏ j ∈ s, v j i z J) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Has.one.congr (fun _ _ _ => Finset.prod_empty.symm) (fun _ _ _ _ => Finset.prod_empty.symm)
  | insert j s hj ih =>
    exact ((h j).mul ih).congr (fun _ _ _ => by beta_reduce; rw [Finset.prod_insert hj]) (fun _ _ _ _ => by
      beta_reduce; rw [Finset.prod_insert hj])

theorem Has.gen (hL : L.IsLB) {F v} (h : Has L r F v) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (hF : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), F U h = ∏ k, h (φ k) ^ ε k) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧ ∀ i z J, Good L z J → val t (r i) z J = v i z J := by
  obtain ⟨K', _, φ', ε', t, ht, hf, hw⟩ := h
  obtain ⟨t', ht', hv⟩ := exists_gen hL (φ' := φ) (ε' := ε) (fun U _ h => (hf U h).trans (hF U h)) t ht
  exact ⟨t', ht', fun i z J hJ => (hv _ _ z J hJ).trans (hw i z J hJ)⟩

end Has

section Comb

variable {R : Type} [CommRing R] [IsDomain R] (Q : Data R)

def lamF {S : Scheme.{0}} {B T : Over S} [GrpObj B] (x y : T ⟶ B) (U : Type) [CommGroup U]
    (h : (T.left ⟶ B.left) → U) : U :=
  h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : T ⟶ B).left

abbrev pt (p : Q.X × Q.X) : (TK R).left ⟶ (G2 Q.B).left :=
  (lift (toUnit (TK R) ≫ Q.c p.1) (toUnit (TK R) ≫ Q.c p.2) : TK R ⟶ G2 Q.B).left

theorem c_zsmul (n : ℤ) (b : Q.X) : Q.c (n • b) = Q.c b ^ n :=
  congrArg Additive.toMul (map_zsmul (PowLim.cHom Q) n b)

theorem has_step (n : ℤ) : Has Q.M.L (pt Q)
    (fun U _ h => lamF (fst Q.B Q.B) (snd Q.B Q.B ^ (n + 1)) U h * (lamF (fst Q.B Q.B) (snd Q.B Q.B ^ n) U h)⁻¹ *
      (lamF (fst Q.B Q.B) (snd Q.B Q.B) U h)⁻¹)
    (fun p z J => (val (Q.tau p.1 ((n + 1) • p.2)) (𝟙 _) z J)⁻¹ * val (Q.tau p.1 (n • p.2)) (𝟙 _) z J *
      val (Q.tau p.1 p.2) (𝟙 _) z J) := by
  refine ⟨_, inferInstance, _, _, LB.pullGen Q.M.L (thφ Q.B (x3 Q.B)) thε Q.cub.t
    (lift (snd Q.B Q.B ^ n) (lift (snd Q.B Q.B) (fst Q.B Q.B))).left, DVR.pullGen_isGen _ _ _ _ Q.cub.isGen _,
    fun U _ h => ?_, fun p z J hJ => ?_⟩
  · refine (prod_cub _ _ _ h).trans ?_
    simp only [lamF]
    rw [zpow_add_one, mul_comm (fst Q.B Q.B), mul_comm (fst Q.B Q.B), mul_comm (fst Q.B Q.B)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · refine (val_cub Q.cub _ hJ _ _ _).trans ?_
    have e := Q.tau_add (n • p.2) p.2 p.1 z J hJ
    have e₁ : lift (toUnit (TK R) ≫ Q.c p.1) (toUnit (TK R) ≫ Q.c p.2) ≫ snd Q.B Q.B ^ n =
        toUnit (TK R) ≫ Q.c (n • p.2) := by
      rw [c_zsmul]
      refine (map_zpow (preHom (lift (toUnit (TK R) ≫ Q.c p.1) (toUnit (TK R) ≫ Q.c p.2))) (snd Q.B Q.B) n).trans
        (Eq.trans ?_ (map_zpow (preHom (toUnit (TK R))) (Q.c p.2) n).symm)
      exact congrArg (· ^ n) (lift_snd (toUnit (TK R) ≫ Q.c p.1) (toUnit (TK R) ≫ Q.c p.2))
    rw [e₁, lift_snd, lift_fst]
    rw [Q.tau_symm _ p.1 z J hJ, Q.tau_symm _ p.1 z J hJ, Q.tau_symm _ p.1 z J hJ] at e
    beta_reduce
    rw [add_smul, one_smul, _root_.mul_assoc, ← e, inv_mul_cancel_left]

theorem has_zpow (n : ℤ) : Has Q.M.L (pt Q)
    (fun U _ h => lamF (fst Q.B Q.B) (snd Q.B Q.B ^ n) U h * (lamF (fst Q.B Q.B) (snd Q.B Q.B) U h ^ n)⁻¹)
    (fun p z J => (val (Q.tau p.1 (n • p.2)) (𝟙 _) z J)⁻¹ * val (Q.tau p.1 p.2) (𝟙 _) z J ^ n) := by
  induction n using Int.induction_on with
  | zero =>
    refine Has.one.congr (fun U _ h => by simp [lamF]) (fun p z J hJ => ?_)
    rw [zero_smul, Q.tau_symm _ _ z J hJ, Q.val_tau_zero _ z J hJ]; simp
  | succ n ih =>
    refine (ih.mul (has_step Q n)).congr (fun U _ h => ?_) (fun p z J hJ => ?_)
    all_goals
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      module
  | pred n ih =>
    have hs := has_step Q (-n - 1)
    rw [sub_add_cancel] at hs
    refine (ih.mul hs.inv).congr (fun U _ h => ?_) (fun p z J hJ => ?_)
    all_goals
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      module

theorem has_comb {r : ℕ} (e c : Fin r → ℤ) (h1 : ∑ j, e j * c j = 1) : Has Q.M.L (pt Q)
    (fun U _ h => (∏ j, lamF (fst Q.B Q.B) (snd Q.B Q.B ^ c j) U h ^ e j) * (lamF (fst Q.B Q.B) (snd Q.B Q.B) U h)⁻¹)
    (fun p z J => (∏ j, val (Q.tau p.1 (c j • p.2)) (𝟙 _) z J ^ e j)⁻¹ * val (Q.tau p.1 p.2) (𝟙 _) z J) := by
  have key : ∀ (U : Type) [CommGroup U] (u : U), ∏ j, (u ^ c j) ^ e j = u := fun U _ u => by
    have : ∀ (s : Finset (Fin r)), ∏ j ∈ s, (u ^ c j) ^ e j = u ^ (∑ j ∈ s, e j * c j) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, zpow_add, ih, ← zpow_mul, mul_comm (c x)]
    rw [this, h1, zpow_one]
  refine (Has.prod (fun j => (has_zpow Q (c j)).zpow (e j)) Finset.univ).congr (fun U _ h => ?_) (fun p z J hJ => ?_)
  · simp only [mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib, key]
  · simp only [mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib, key]

end Comb

end GlobalTheory.Mum.PolPair

namespace GlobalTheory.Mum.PolPair

abbrev cQ {R : Type} [CommRing R] [IsDomain R] (Q : Data R) (a : Q.X) : TK R ⟶ Q.B := toUnit (TK R) ≫ Q.c a

theorem cQ_add {R : Type} [CommRing R] [IsDomain R] (Q : Data R) (a b : Q.X) : cQ Q (a + b) = cQ Q a * cQ Q b := by
  rw [cQ, Q.c_add, MonObj.comp_mul]


open ReciprocityTheory.ChartRestriction.G.DVR in
open GlobalTheory.Mum.TensPer in
theorem tau_periods : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (Q : Data R) (D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.toPre.P.A ⟶ Q.B)) (xe : D'.toPre.X ≃+ (Fin r → Q.X)) (w : LB.Iso D'.toPre.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), (∀ z i, D'.toPre.c z ≫ pr i = Q.c (xe z i)) → (∀ y z J J', Good Q.M.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.psi y) (𝟙 _) z J' = gm (D'.toPre.xK y) z _ (w.s (fun k => J (D'.toPre.xK y ≫ tensφ pr k), J' (D'.toPre.xK y))) * ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) → ∀ (a b : D'.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ Q.B.left) → Q.M.L.ι) (J' : ((TK R).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good Q.M.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = (∏ K : ULift.{0} (Finset (Fin 2)), gm ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left) z _ (w.s (fun k => J ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left ≫ tensφ pr k), J' ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left))) ^ ((-1 : ℤ) ^ (2 - K.down.card))) * (∏ i, ∏ j, (cubV Q.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ pr i) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ pr i) ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ pr j) * (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ pr j)) * cubV Q.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ pr i) * cubV Q.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ pr i)) ^ (-W i j)) * ∏ i, ∏ j, val (Q.tau (xe a i) (xe b j)) (𝟙 _) z J ^ ((W + W.transpose) i j) := by
  intro R _ _ I Q D' r W pr xe w hc hψ a b z J J' hJ hJ'
  have twist_vector_at_zero : ∀ (E : DegData R I) (K : ((TK R).left ⟶ E.toPre.P.A.left) → E.toPre.P.L.ι),
      Good E.toPre.P.L z K → val (E.toPre.tau 0 0) (𝟙 _) z K = 1 := by
    intro E K hK
    have e := GlobalTheory.TauTwist.val_tau_add (𝟙 (TK R)) hK E.tau_bimult 0 0 0
    have f : th E.toPre z K (cP E.toPre (TK R) 0) (cP E.toPre (TK R) 0) (cP E.toPre (TK R) 0) = 1 := by
      rw [cPoint_zero]; exact (isCub_cubV E.toPre.cub hK).face 1 1
    rw [f, _root_.mul_one] at e
    have h0 : val (E.toPre.tau (0 + 0) 0) (𝟙 _) z K = val (E.toPre.tau 0 0) (𝟙 _) z K :=
      congrArg (fun x => val (E.toPre.tau x 0) (𝟙 _) z K) (add_zero 0)
    exact mul_eq_left.1 (e.symm.trans h0)
  have hadd : ∀ x x' y : Q.X, val (Q.tau (x + x') y) (𝟙 _) z J *
      cubV Q.cub z J (cQ Q x) (cQ Q x') (cQ Q y) =
      val (Q.tau x y) (𝟙 _) z J * val (Q.tau x' y) (𝟙 _) z J :=
    fun x x' y => Q.tau_add x x' y z J hJ
  have hsym : ∀ x y : Q.X, val (Q.tau x y) (𝟙 _) z J = val (Q.tau y x) (𝟙 _) z J :=
    fun x y => Q.tau_symm x y z J hJ
  set ρ : TK R ⟶ D'.toPre.P.A ⊗ D'.toPre.P.A :=
    lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) with hρ
  have wv : ∀ (q : (D'.toPre.P.A ⊗ D'.toPre.P.A).left ⟶ D'.toPre.P.A.left) (y : D'.toPre.X),
      ρ.left ≫ q = D'.toPre.xK y →
      gm (ρ.left ≫ q) z _ (w.s (fun k => J (ρ.left ≫ q ≫ tensφ pr k), J' (ρ.left ≫ q))) =
      gm (D'.toPre.xK y) z _ (w.s (fun k => J (D'.toPre.xK y ≫ tensφ pr k), J' (D'.toPre.xK y))) := by
    intro q y h
    have gen : ∀ m m' j j', m = m' → j = j' → gm m z _ (w.s j) = gm m' z _ (w.s j') := by
      rintro _ _ _ _ rfl rfl; rfl
    refine gen _ _ _ _ h ?_
    refine Prod.ext ?_ ?_
    · dsimp only
      funext k
      rw [← Category.assoc, h]
    · dsimp only
      rw [h]
  have hE : ρ.left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) ∅).left = D'.toPre.xK 0 := by
    rw [← Over.comp_left]
    show _ = (cP D'.toPre (TK R) 0).left
    rw [groupSchemePartialSum_twoPoints_empty, cPoint_zero, MonObj.comp_one]
  have h₀ : ρ.left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) {0}).left = D'.toPre.xK a := by
    rw [← Over.comp_left]
    show _ = (cP D'.toPre (TK R) a).left
    rw [groupSchemePartialSum_twoPoints_first, MonObj.comp_mul, MonObj.comp_one, _root_.mul_one, hρ, lift_fst]; rfl
  have h₁ : ρ.left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) {1}).left = D'.toPre.xK b := by
    rw [← Over.comp_left]
    show _ = (cP D'.toPre (TK R) b).left
    rw [groupSchemePartialSum_twoPoints_second, MonObj.comp_mul, MonObj.comp_one, _root_.mul_one, hρ, lift_snd]; rfl
  have h₂ : ρ.left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) {0, 1}).left = D'.toPre.xK (a + b) := by
    rw [← Over.comp_left]
    show _ = (cP D'.toPre (TK R) (a + b)).left
    rw [groupSchemePartialSum_twoPoints_both, MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_one, _root_.mul_one, hρ, lift_fst, lift_snd, cPoint_add]; rfl
  have hA : ∀ i, ρ ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ pr i = cQ Q (xe a i) := fun i => by
    rw [hρ, lift_fst_assoc, Category.assoc, hc]
  have hB : ∀ i, ρ ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ pr i = cQ Q (xe b i) := fun i => by
    rw [hρ, lift_snd_assoc, Category.assoc, hc]
  have P := prod_psum_two (G := D'.toPre.P.A)
    (fun q => gm (ρ.left ≫ q) z _ (w.s (fun k => J (ρ.left ≫ q ≫ tensφ pr k), J' (ρ.left ≫ q))))
  beta_reduce at P
  rw [P]
  rw [wv _ _ h₂, wv _ _ h₀, wv _ _ h₁, wv _ _ hE]
  simp only [hA, hB]
  rw [GlobalTheory.TauBalBox.tau_val D'.toPre hJ' a b (𝟙 _)]
  have hrig : (val D'.toPre.rigK (𝟙 _) z J')⁻¹ = val (D'.toPre.psi 0) (𝟙 _) z J' := by
    have e := GlobalTheory.TauBalBox.tau_val D'.toPre hJ' 0 0 (𝟙 _)
    rw [twist_vector_at_zero D' J' hJ'] at e
    have h0 : val (D'.toPre.psi (0 + 0)) (𝟙 _) z J' = val (D'.toPre.psi 0) (𝟙 _) z J' :=
      congrArg (fun x => val (D'.toPre.psi x) (𝟙 _) z J') (add_zero 0)
    rw [h0, mul_inv_cancel, _root_.one_mul] at e
    exact (inv_mul_eq_one.1 e.symm).symm
  rw [hrig, hψ (a + b) z J J' hJ hJ', hψ a z J J' hJ hJ', hψ b z J J' hJ hJ', hψ 0 z J J' hJ hJ']
  have hQ0 : ∏ i, ∏ j, val (Q.tau (xe 0 i) (xe 0 j)) (𝟙 _) z J ^ W i j = 1 :=
    Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => by
      rw [show xe 0 = 0 from map_zero _]
      exact (congrArg (· ^ W i j) (Q.val_tau_zero 0 z J hJ)).trans (one_zpow _)
  have hQab : ∏ i, ∏ j, val (Q.tau (xe (a + b) i) (xe (a + b) j)) (𝟙 _) z J ^ W i j =
      ∏ i, ∏ j, val (Q.tau (xe a i + xe b i) (xe a j + xe b j)) (𝟙 _) z J ^ W i j := by
    rw [map_add (f := _)]; rfl
  rw [hQ0, hQab]
  have key := periods_alg (cQ Q) (cQ_add Q)
    (fun x y => val (Q.tau x y) (𝟙 _) z J) (cubV Q.cub z J) hsym hadd W (xe a) (xe b)
  beta_reduce at key
  apply Additive.ofMul.injective
  have k := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at k ⊢
  linear_combination (norm := abel) k

theorem lam_core : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (Q : Data R) (D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.toPre.P.A ⟶ Q.B)) (xe : D'.toPre.X ≃+ (Fin r → Q.X)) (w : LB.Iso D'.toPre.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), (∀ z i, D'.toPre.c z ≫ pr i = Q.c (xe z i)) → (∀ y z J J', Good Q.M.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.psi y) (𝟙 _) z J' = gm (D'.toPre.xK y) z _ (w.s (fun k => J (D'.toPre.xK y ≫ tensφ pr k), J' (D'.toPre.xK y))) * ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) → (∀ i, IsMonHom (pr i)) → w.IsGen → ∃ w₁ : LB.Iso (abelian₂ D'.toPre.P.A D'.toPre.P.L) (LB.LinComb Q.M.L (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ pr k.1.2) k.2) (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2)), w₁.IsGen ∧ ∀ (a b : D'.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ Q.B.left) → Q.M.L.ι) (J' : ((TK R).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good Q.M.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = gm (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z _ (w₁.s (fun k => J ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ pr k.1.2) k.2), fun I => J' ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left))) * ∏ i, ∏ j, val (Q.tau (xe a i) (xe b j)) (𝟙 _) z J ^ ((W + W.transpose) i j) := by
  intro R _ _ I Q D' r W pr xe w hc hψ hpr hw
  obtain ⟨v, hv, hvv⟩ := GlobalTheory.Mum.exists_transIso_linComb (L := Q.M.L) (L' := D'.toPre.P.L) (tensφ pr) (tensε W) w hw
    Q.M.isLB D'.toPre.P.isLB
    (fun K : ULift.{0} (Finset (Fin 2)) => (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left)
    (fun K => (-1 : ℤ) ^ (2 - K.down.card))
  obtain ⟨c, hc', hcv⟩ := GlobalTheory.Mum.cube_step Q.M
    Q.cub W pr hpr
  obtain ⟨u, hu, huv⟩ := GlobalTheory.LinCombComp.exists_iso_comp_val (A := abelian₂ D'.toPre.P.A D'.toPre.P.L) _ _
    (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ pr k.1.1)
      (snd D'.toPre.P.A D'.toPre.P.A ≫ pr k.1.2) k.2)
    (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2) Q.M.isLB (LB.isLB_linComb D'.toPre.P.isLB _ _) v hv c hc'
  refine ⟨u, hu, fun a b z J J' hJ hJ' => ?_⟩
  have e1 := hvv _ (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z J J' hJ hJ'
  have e2 := hcv (TK R) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)) z J hJ
  rw [huv _ _ z J _ (hJ'.mem _ _) hJ, e2]
  refine (tau_periods R I Q D' W pr xe w hc hψ a b z J J' hJ hJ').trans ?_
  exact congrArg (· * _) (congrArg (· * _) e1.symm)

end GlobalTheory.Mum.PolPair

namespace GlobalTheory.Mum.PolPair

theorem exists_comb {R : Type} [CommRing R] [IsDomain R] (Q : Data R) {r : ℕ} (e c : Fin r → ℤ) (h1 : ∑ j, e j * c j = 1) :
    ∃ u : LB.Gen (LB.LinComb Q.M.L
        (Sum.elim (fun q : Fin r × Fin 4 => GlobalTheory.PolDeg.lamPts (fst Q.B Q.B) (snd Q.B Q.B ^ c q.1) q.2)
          (fun I : ULift (Finset (Fin 2)) => (psum Q.B (x2 Q.B) I.down).left))
        (Sum.elim (fun q => e q.1 * Oε q.2) (fun I => -((-1) ^ (2 - I.down.card))))), u.IsGen ∧
      ∀ (a b : Q.X) (z : (TK R).left) (J : ((TK R).left ⟶ Q.B.left) → Q.M.L.ι), Good Q.M.L z J →
        val (Q.tau a b) (𝟙 _) z J = val u (lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b)).left z J *
          ∏ j, val (Q.tau a (c j • b)) (𝟙 _) z J ^ e j := by
  obtain ⟨u, hu, hv⟩ := (has_comb Q e c h1).gen Q.M.isLB
    (Sum.elim (fun q : Fin r × Fin 4 => GlobalTheory.PolDeg.lamPts (fst Q.B Q.B) (snd Q.B Q.B ^ c q.1) q.2)
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum Q.B (x2 Q.B) I.down).left))
    (Sum.elim (fun q => e q.1 * Oε q.2) (fun I => -((-1) ^ (2 - I.down.card)))) (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      refine congrArg₂ (· * ·) ?_ (congrArg (·⁻¹) ?_)
      · rw [Fintype.prod_prod_type]
        refine Finset.prod_congr rfl fun j _ => ?_
        refine Eq.trans ?_ (CubeStep.prod_zpow_mul (fun l => h (GlobalTheory.PolDeg.lamPts (fst Q.B Q.B) (snd Q.B Q.B ^ c j) l))
          Oε (e j)).symm
        congr 1
        simp [lamF, Fin.prod_univ_four, GlobalTheory.PolDeg.lamPts, Oε]
      · refine Eq.trans ?_ (TensPer.prod_psum_two h).symm
        rw [CubeStep.groupSchemePartialSum_pair_both, CubeStep.psum0, CubeStep.psum1, CubeStep.psumE]
        rfl)
  refine ⟨u, hu, fun a b z J hJ => ?_⟩
  rw [show val u (lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b)).left z J = _ from hv (a, b) z J hJ,
    mul_right_comm, inv_mul_cancel, _root_.one_mul]

theorem lamPts_pull {R : Type} [CommRing R] [IsDomain R] {Q : Data R} {D' : DegPre R} {r : ℕ}
    (pr : Fin r → (D'.P.A ⟶ Q.B)) (hl : IsLimit (Fan.mk D'.P.A pr)) (i₀ : Fin r) (m : Matrix (Fin r) (Fin r) ℤ) (i j : Fin r) (l : Fin 4) :
    (lift (fst Q.B Q.B ≫ PowLim.inc pr hl i₀) (snd Q.B Q.B ≫ PowLim.inc pr hl i₀ ≫ PowLim.act pr hl m) : G2 Q.B ⟶ G2 D'.P.A).left ≫
      GlobalTheory.PolDeg.lamPts (fst D'.P.A D'.P.A ≫ pr i) (snd D'.P.A D'.P.A ≫ pr j) l =
    GlobalTheory.PolDeg.lamPts (if i = i₀ then fst Q.B Q.B else 1) (snd Q.B Q.B ^ m j i₀) l := by
  have h1 : (lift (fst Q.B Q.B ≫ PowLim.inc pr hl i₀) (snd Q.B Q.B ≫ PowLim.inc pr hl i₀ ≫ PowLim.act pr hl m) : G2 Q.B ⟶ G2 D'.P.A) ≫
      fst D'.P.A D'.P.A ≫ pr i = if i = i₀ then fst Q.B Q.B else 1 := by
    rw [lift_fst_assoc, Category.assoc, PowLim.inc_pr]
    split_ifs <;> simp
  have h2 : (lift (fst Q.B Q.B ≫ PowLim.inc pr hl i₀) (snd Q.B Q.B ≫ PowLim.inc pr hl i₀ ≫ PowLim.act pr hl m) : G2 Q.B ⟶ G2 D'.P.A) ≫
      snd D'.P.A D'.P.A ≫ pr j = snd Q.B Q.B ^ m j i₀ := by
    rw [lift_snd_assoc, Category.assoc, Category.assoc, PowLim.act_pr]
    have e : ∀ k, (snd Q.B Q.B ≫ PowLim.inc pr hl i₀) ≫ pr k = if k = i₀ then snd Q.B Q.B else 1 := fun k => by
      rw [Category.assoc, PowLim.inc_pr]; split_ifs <;> simp
    rw [← Category.assoc]
    change preHom (snd Q.B Q.B ≫ PowLim.inc pr hl i₀) (∏ k, pr k ^ m j k) = _
    rw [map_prod]
    simp only [map_zpow]
    change ∏ k, ((snd Q.B Q.B ≫ PowLim.inc pr hl i₀) ≫ pr k) ^ m j k = _
    simp only [e]
    rw [Finset.prod_eq_single i₀ (fun k _ hk => by rw [if_neg hk, one_zpow]) (by simp), if_pos rfl]
  rw [GlobalTheory.TensPair.lamPts_comp, h1, h2]

theorem xe_xi {R : Type} [CommRing R] [IsDomain R] {Q : Data R} {D' : DegPre R} {r : ℕ}
    (xe : D'.X ≃+ (Fin r → Q.X)) (i₀ i : Fin r) (a : Q.X) : xe (PowLim.xi xe i₀ a) i = if i = i₀ then a else 0 := by
  simp [PowLim.xi, Pi.single_apply]

theorem pt_pull {R : Type} [CommRing R] [IsDomain R] {Q : Data R} {D' : DegPre R} {r : ℕ}
    (pr : Fin r → (D'.P.A ⟶ Q.B)) (hl : IsLimit (Fan.mk D'.P.A pr)) (xe : D'.X ≃+ (Fin r → Q.X))
    (hc : ∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) (i₀ : Fin r) (m : Matrix (Fin r) (Fin r) ℤ) (a b : Q.X) (a' b' : D'.X)
    (ha : ∀ i, xe a' i = if i = i₀ then a else 0) (hb : ∀ j, xe b' j = m j i₀ • b) :
    (lift (toUnit (TK R) ≫ D'.c a') (toUnit (TK R) ≫ D'.c b') : TK R ⟶ G2 D'.P.A) =
      lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) ≫
        lift (fst Q.B Q.B ≫ PowLim.inc pr hl i₀) (snd Q.B Q.B ≫ PowLim.inc pr hl i₀ ≫ PowLim.act pr hl m) := by
  have c0 : Q.c 0 = 1 := by
    have := c_zsmul Q 0 a; rwa [zero_smul, zpow_zero] at this
  rw [comp_lift, lift_fst_assoc, lift_snd_assoc]
  congr 1
  · refine PowLim.hom_ext pr hl fun i => ?_
    simp only [Category.assoc]
    rw [hc, ha, PowLim.inc_pr]
    split_ifs <;> simp [c0]
  · refine PowLim.hom_ext pr hl fun i => ?_
    simp only [Category.assoc]
    rw [hc, hb, c_zsmul, PowLim.act_pr]
    have e : ∀ k, (toUnit (TK R) ≫ Q.c b ≫ PowLim.inc pr hl i₀) ≫ pr k = if k = i₀ then toUnit (TK R) ≫ Q.c b else 1 := fun k => by
      rw [Category.assoc, Category.assoc, PowLim.inc_pr]; split_ifs <;> simp
    calc toUnit (TK R) ≫ Q.c b ^ m i i₀ = (toUnit (TK R) ≫ Q.c b) ^ m i i₀ := map_zpow (preHom (toUnit (TK R))) _ _
      _ = ∏ k, ((toUnit (TK R) ≫ Q.c b ≫ PowLim.inc pr hl i₀) ≫ pr k) ^ m i k := by
        simp only [e]
        rw [Finset.prod_eq_single i₀ (fun k _ hk => by rw [if_neg hk, one_zpow]) (by simp), if_pos rfl]
      _ = (toUnit (TK R) ≫ Q.c b ≫ PowLim.inc pr hl i₀) ≫ ∏ k, pr k ^ m i k := by
        change _ = preHom (toUnit (TK R) ≫ Q.c b ≫ PowLim.inc pr hl i₀) (∏ k, pr k ^ m i k)
        rw [map_prod]
        simp only [map_zpow]
        rfl
      _ = _ := by simp only [Category.assoc]

theorem pairing_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegData R (maximalIdeal R))
    {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef →
    ∀ (pr : Fin r → (D'.toPre.P.A ⟶ Q.B)) (hl : IsLimit (Fan.mk D'.toPre.P.A pr)) (xe : D'.toPre.X ≃+ (Fin r → Q.X))
    (w : LB.Iso D'.toPre.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))),
    (∀ i, IsMonHom (pr i)) → (∀ z i, D'.toPre.c z ≫ pr i = Q.c (xe z i)) → w.IsGen →
    (∀ y z J J', Good Q.M.L z J → Good D'.toPre.P.L z J' →
      val (D'.toPre.psi y) (𝟙 _) z J' = gm (D'.toPre.xK y) z _ (w.s (fun k => J (D'.toPre.xK y ≫ tensφ pr k), J' (D'.toPre.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) →
    ∀ i₀ : Fin r,
    letI := PowLim.mod xe (symUnitOf W h)
    ∃ w' : LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ D'.toPre.P.A D'.toPre.P.L).pull
      (lift (fst Q.B Q.B ≫ PowLim.inc pr hl i₀) (snd Q.B Q.B ≫ PowLim.inc pr hl i₀ ≫
        PowLim.act pr hl (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 Q.B ⟶ G2 D'.toPre.P.A).left),
      w'.IsGen ∧ ∀ a b z J J', Good D'.toPre.P.L z J → Good Q.M.L z J' →
        val (Q.tau a b) (𝟙 _) z J' =
          lamVal w' (lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b)).left z J J' *
            val (D'.toPre.tau (PowLim.xi xe i₀ a) (TensO.binv (symUnitOf W h) • PowLim.xi xe i₀ b)) (𝟙 _) z J := by
  intro R _ _ _ _ Q D' r W h _ pr hl xe w₀ hpr hc hw₀ hψ i₀
  obtain ⟨w₁, hw₁, hv₁⟩ := lam_core R _ Q D' W pr xe w₀ hc hψ hpr hw₀
  clear hψ hw₀ w₀
  have hsum : ∑ j, (W + W.transpose) i₀ j * TensO.mat _ (TensO.binv (symUnitOf W h)) j i₀ = 1 := by
    have hb : (((symUnitOf W h).1 : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) = W + W.transpose :=
      IsUnit.unit_spec _
    have key := congrFun (congrFun (Units.mul_inv (symUnitOf W h).1) i₀) i₀
    rw [hb, Matrix.mul_apply, Matrix.one_apply_eq] at key
    exact key
  obtain ⟨u₀, hu₀, hv₀⟩ := exists_comb Q (fun j => (W + W.transpose) i₀ j)
    (fun j => TensO.mat _ (TensO.binv (symUnitOf W h)) j i₀) hsum
  obtain ⟨u, hu, hvu⟩ := exists_gen Q.M.isLB
    (φ' := Sum.elim (fun k : (Fin r × Fin r) × Fin 4 => (lift (fst Q.B Q.B ≫ PowLim.inc pr hl i₀) (snd Q.B Q.B ≫ PowLim.inc pr hl i₀ ≫ PowLim.act pr hl (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 Q.B ⟶ G2 D'.toPre.P.A).left ≫ GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ pr k.1.2) k.2) (fun I : ULift (Finset (Fin 2)) => (psum Q.B (x2 Q.B) I.down).left))
    (ε' := Sum.elim (fun k : (Fin r × Fin r) × Fin 4 => (W + W.transpose) k.1.1 k.1.2 * Oε k.2) (fun I : ULift (Finset (Fin 2)) => -((-1) ^ (2 - I.down.card))))
    (fun U _ hh => by
      clear hv₀ hv₁ hu₀ u₀ hw₁ w₁
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      refine congrArg (· * _) ?_
      simp only [Sum.elim_inl, lamPts_pull, Fintype.prod_prod_type]
      symm
      rw [Finset.prod_eq_single i₀ ?_ (by simp)]
      · exact Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun l _ => by rw [if_pos rfl]
      · intro i _ hi
        refine Finset.prod_eq_one fun j _ => ?_
        rw [Fin.prod_univ_four, if_neg hi]
        simp only [GlobalTheory.PolDeg.lamPts, Oε, _root_.one_mul]
        simp
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_zpow, ofMul_one]
        module)
    u₀ hu₀
  obtain ⟨w, hw, hvw⟩ := GlobalTheory.Mum.iso_linComb_pull_glue Q.M.isLB (LB.isLB_linComb D'.toPre.P.isLB _ _) _ _ _ _ _ w₁ hw₁ u hu
  refine ⟨w, hw, fun a b z J J' hJ hJ' => ?_⟩

  suffices key : ∀ b' : D'.toPre.X, (∀ j, xe b' j = TensO.mat _ (TensO.binv (symUnitOf W h)) j i₀ • b) →
      val (Q.tau a b) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) : TK R ⟶ G2 Q.B).left z J J' *
        val (D'.toPre.tau (PowLim.xi xe i₀ a) b') (𝟙 _) z J by
    exact key _ (fun j => (PowLim.xe_smul xe (symUnitOf W h) (TensO.binv _) (PowLim.xi xe i₀ b) j).trans (by
      rw [Finset.sum_eq_single i₀ (fun k _ hk => by rw [xe_xi, if_neg hk, smul_zero]) (by simp),
        xe_xi, if_pos rfl]))
  intro b' hb'
  have hPl : (lift (toUnit (TK R) ≫ D'.toPre.c (PowLim.xi xe i₀ a)) (toUnit (TK R) ≫ D'.toPre.c b') : TK R ⟶ G2 D'.toPre.P.A).left =
      (lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) : TK R ⟶ G2 Q.B).left ≫
        (lift (fst Q.B Q.B ≫ PowLim.inc pr hl i₀) (snd Q.B Q.B ≫ PowLim.inc pr hl i₀ ≫ PowLim.act pr hl (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 Q.B ⟶ G2 D'.toPre.P.A).left := by
    rw [pt_pull pr hl xe hc i₀ _ a b _ b' (xe_xi xe i₀ · a) hb']; rfl
  have t0 : ∀ x, val (Q.tau 0 x) (𝟙 _) z J' = 1 := fun x => Q.val_tau_zero x z J' hJ'
  have hPi : ∏ i, ∏ j, val (Q.tau (xe (PowLim.xi xe i₀ a) i) (xe b' j)) (𝟙 _) z J' ^ ((W + W.transpose) i j) =
      ∏ j, val (Q.tau a (TensO.mat _ (TensO.binv (symUnitOf W h)) j i₀ • b)) (𝟙 _) z J' ^ ((W + W.transpose) i₀ j) := by
    rw [Finset.prod_eq_single i₀ (fun i _ hi => Finset.prod_eq_one fun j _ => by
      rw [xe_xi, if_neg hi, t0, one_zpow]) (by simp)]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [xe_xi, if_pos rfl, hb']
  have e1 := hv₁ (PowLim.xi xe i₀ a) b' z J' J hJ' hJ
  rw [hPi, hPl] at e1
  have e2 := hvw _ (lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) : TK R ⟶ G2 Q.B).left z J' hJ'
    (fun I => J (((lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) : TK R ⟶ G2 Q.B).left ≫
        (lift (fst Q.B Q.B ≫ PowLim.inc pr hl i₀) (snd Q.B Q.B ≫ PowLim.inc pr hl i₀ ≫ PowLim.act pr hl (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 Q.B ⟶ G2 D'.toPre.P.A).left) ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left))
    (hJ.mem _ _)
  have e3 := hv₀ a b z J' hJ'
  have e4 := hvu _ (lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) : TK R ⟶ G2 Q.B).left z J' hJ'
  clear hv₀ hvu hvw hv₁ hPi
  change val _ _ z J = gv w₁ _ z _ _ * _ at e1
  have hj : (fun I : ULift (Finset (Fin 2)) => J ((lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) : TK R ⟶ G2 Q.B).left ≫ (lift (fst Q.B Q.B ≫ PowLim.inc pr hl i₀) (snd Q.B Q.B ≫ PowLim.inc pr hl i₀ ≫ PowLim.act pr hl (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 Q.B ⟶ G2 D'.toPre.P.A).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left)) =
      (fun I => J (((lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) : TK R ⟶ G2 Q.B).left ≫ (lift (fst Q.B Q.B ≫ PowLim.inc pr hl i₀) (snd Q.B Q.B ≫ PowLim.inc pr hl i₀ ≫ PowLim.act pr hl (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 Q.B ⟶ G2 D'.toPre.P.A).left) ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left)) :=
    funext fun I => by rw [Category.assoc]
  have e5 : GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) : TK R ⟶ G2 Q.B).left z J J' = gw w (lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) : TK R ⟶ G2 Q.B).left z (fun I : ULift (Finset (Fin 2)) => J ((lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) : TK R ⟶ G2 Q.B).left ≫ (lift (fst Q.B Q.B ≫ PowLim.inc pr hl i₀) (snd Q.B Q.B ≫ PowLim.inc pr hl i₀ ≫ PowLim.act pr hl (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 Q.B ⟶ G2 D'.toPre.P.A).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left))
      (fun I => J' ((lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) : TK R ⟶ G2 Q.B).left ≫ (psum Q.B (x2 Q.B) I.down).left)) := rfl
  rw [e5, hj, e2, e1, e3, e4]
  have key : ∀ {G : Type} [CommGroup G] (A P X : G), A * P = X⁻¹ * A * (X * P) := fun A P X => by
    rw [_root_.mul_comm X⁻¹ A, _root_.mul_assoc, inv_mul_cancel_left]
  exact key (G := ((TK R).left.presheaf.stalk z)ˣ) _ _ _

end GlobalTheory.Mum.PolPair
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordIsoPeriodsFactorTensorPolarised =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordIsoPeriodsFactorTensorPolarisedStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordIsoPeriodsFactorTensorPolarisedStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgIdemBinv\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordIsoPeriodsFactorTensorPolarised\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordIsoPeriodsFactorTensorPolarisedStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTrivialMumfordFormalSumLatticeAdditivityRelati =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTrivialMumfordFormalSumLatticeAdditivityRelati", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgIdemBinv\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosVec\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStronglyTrivialCubicalThetaFinsuppTensor\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataMatrixActionRingHomProperties\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedGeneratorUniqueGlobalFunctionsBase\npublic import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom\nimport Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TauBalPow\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull\nimport Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.PolTens
open GlobalTheory.TensBal

section Formal
variable {r : ℕ}

abbrev PVec (r : ℕ) := Vec r × Vec r

def flat : (PVec r →₀ ℤ) →+ (Vec r →₀ ℤ) :=
  Finsupp.liftAddHom fun p => zmultiplesHom (Vec r →₀ ℤ) (lam p.1 p.2)

def rel1 (u u' v : Vec r) : PVec r →₀ ℤ :=
  Finsupp.single (u + u', v) 1 - Finsupp.single (u, v) 1 - Finsupp.single (u', v) 1

def rel2 (u v : Vec r) : PVec r →₀ ℤ :=
  Finsupp.single (u, v) 1 - Finsupp.single (v, u) 1

def sigP (W A A' : Matrix (Fin r) (Fin r) ℤ) : PVec r →₀ ℤ :=
  ∑ a : Fin 6, ∑ i, ∑ j, (rosatiε a * W i j) • Finsupp.single (rosVec A A' a i, rosVec A A' a j) 1

def rels (r : ℕ) : Set (PVec r →₀ ℤ) :=
  Set.range (fun p : Vec r × Vec r × Vec r => rel1 p.1 p.2.1 p.2.2) ∪ Set.range (fun p : Vec r × Vec r => rel2 p.1 p.2)

theorem flat_single (u v : Vec r) : flat (Finsupp.single (u, v) 1) = lam u v := by
  simp [flat]

theorem flat_sigP (W A A' : Matrix (Fin r) (Fin r) ℤ) : flat (sigP W A A') = sig W A A' := by

  simp only [sigP, sig, map_sum, map_zsmul, flat_single]

end Formal

section Maps
variable {S : Scheme.{0}} {A B : Over S} [GrpObj B] [IsCommMonObj B] {r : ℕ}

def vecHom (pr : Fin r → (A ⟶ B)) (v : Vec r) : A ⊗ A ⟶ B :=
  (∏ k, (fst A A ≫ pr k) ^ v (Sum.inl k)) * ∏ k, (snd A A ≫ pr k) ^ v (Sum.inr k)

end Maps

def vecLat {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {r : ℕ} (xe : X' ≃+ (Fin r → X)) (v : Vec r)
    (y y' : X') : X :=
  ∑ k, v (Sum.inl k) • xe y k + ∑ k, v (Sum.inr k) • xe y' k

variable {R : Type} [CommRing R] [IsDomain R] {r : ℕ}

def Triv (Q : Data R) (D' : DegPre R) (pr : Fin r → (D'.P.A ⟶ Q.B)) (c : Vec r →₀ ℤ)
    (V : (z : (TK R).left) → (((TK R).left ⟶ Q.B.left) → Q.M.L.ι) → D'.X → D'.X →
      ((TK R).left.presheaf.stalk z)ˣ) : Prop :=
  ∃ Ξ : LB.Gen (LB.LinComb Q.M.L (fun v : c.support => (vecHom pr v.1).left) (fun v => c v.1)), Ξ.IsGen ∧
    (∀ (z : (𝟙_ (Over (Spec (CommRingCat.of R)))).left) J, Good Q.M.L z J → val Ξ (zero2 D'.P.A) z J = 1) ∧
    ∀ (z : (TK R).left) J, Good Q.M.L z J → ∀ y y' : D'.X, val Ξ (D'.pt2 y y') z J = V z J y y'

def tv (Q : Data R) {X' : Type} [AddCommGroup X'] (xe : X' ≃+ (Fin r → Q.X)) (n : PVec r →₀ ℤ) (z : (TK R).left)
    (J : ((TK R).left ⟶ Q.B.left) → Q.M.L.ι) (y y' : X') : ((TK R).left.presheaf.stalk z)ˣ :=
  n.prod fun p k => val (Q.tau (vecLat xe p.1 y y') (vecLat xe p.2 y y')) (𝟙 _) z J ^ (-k)

end GlobalTheory.Mum.PolTens

noncomputable section
namespace GlobalTheory.Mum.PolTens
open GlobalTheory.TensBal

variable {R : Type} [CommRing R] [IsDomain R] {r : ℕ}

section Maps
variable {S : Scheme.{0}} {A B : Over S} [GrpObj B] [IsCommMonObj B]

theorem vecHom_add (pr : Fin r → (A ⟶ B)) (u v : Vec r) : vecHom pr (u + v) = vecHom pr u * vecHom pr v := by
  simp only [vecHom, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  exact mul_mul_mul_comm _ _ _ _

theorem vecHom_zero (pr : Fin r → (A ⟶ B)) : vecHom pr 0 = 1 := by
  simp only [vecHom, Pi.zero_apply, zpow_zero, Finset.prod_const_one, _root_.mul_one]

theorem comp_vecHom (pr : Fin r → (A ⟶ B)) {Z : Over S} (p q : Z ⟶ A) (v : Vec r) :
    lift p q ≫ vecHom pr v = (∏ k, (p ≫ pr k) ^ v (Sum.inl k)) * ∏ k, (q ≫ pr k) ^ v (Sum.inr k) := by
  rw [vecHom, MonObj.comp_mul, GlobalTheory.Mum.TensAct.comp_prod_zpow, GlobalTheory.Mum.TensAct.comp_prod_zpow]
  simp only [lift_fst_assoc, lift_snd_assoc]

end Maps

theorem vecLat_add {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (xe : X' ≃+ (Fin r → X)) (u v : Vec r) (y y' : X') :
    vecLat xe (u + v) y y' = vecLat xe u y y' + vecLat xe v y y' := by
  simp only [vecLat, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  abel

end GlobalTheory.Mum.PolTens

namespace GlobalTheory.Mum.PolTens
open GlobalTheory.TensBal

variable {R : Type} [CommRing R] [IsDomain R] {r : ℕ}

theorem prod_support_eq {U : Type} [CommGroup U] (g : Vec r → ℤ → U) (d : Vec r →₀ ℤ) :
    ∏ v : d.support, g v.1 (d v.1) = d.prod g :=
  Finset.prod_coe_sort d.support (fun v => g v (d v))

variable (Q : Data R) (D' : DegPre R) (pr : Fin r → (D'.P.A ⟶ Q.B))

theorem triv_zero : Triv Q D' pr 0 (fun _ _ _ _ => 1) := by
  obtain ⟨t, ht, hv⟩ := exists_gen Q.M.isLB
    (φ' := fun v : (0 : Vec r →₀ ℤ).support => (vecHom pr v.1).left) (ε' := fun v => (0 : Vec r →₀ ℤ) v.1)
    (fun U _ h => by simp) (LB.oneGen Q.M.L (Y := (D'.P.A ⊗ D'.P.A).left)) (LB.isGen_oneGen _)
  refine ⟨t, ht, fun z J hJ => (hv _ _ z J hJ).trans (val_one _), fun z J hJ y y' => ?_⟩
  rw [hv _ _ z J hJ, val_one]

variable {Q D' pr}

theorem triv_add {c c' : Vec r →₀ ℤ} {V V'} (h : Triv Q D' pr c V) (h' : Triv Q D' pr c' V') :
    Triv Q D' pr (c + c') (fun z J y y' => V z J y y' * V' z J y y') := by
  obtain ⟨Ξ, hΞ, h1, h2⟩ := h
  obtain ⟨Ξ', hΞ', h1', h2'⟩ := h'
  have hform : FormEq (Sum.elim (fun v : c.support => (vecHom pr v.1).left) (fun v : c'.support => (vecHom pr v.1).left))
      (Sum.elim (fun v : c.support => c v.1) (fun v : c'.support => c' v.1))
      (fun v : (c + c').support => (vecHom pr v.1).left) (fun v => (c + c') v.1) := by
    intro U _ h
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [prod_support_eq (fun v n => h (vecHom pr v).left ^ n) c,
      prod_support_eq (fun v n => h (vecHom pr v).left ^ n) c',
      prod_support_eq (fun v n => h (vecHom pr v).left ^ n) (c + c'),
      Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun _ _ _ => zpow_add _ _ _)]
  obtain ⟨Ξ'', hΞ'', hv⟩ := exists_gen Q.M.isLB hform _
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ hΞ hΞ')
  refine ⟨Ξ'', hΞ'', fun z J hJ => ?_, fun z J hJ y y' => ?_⟩
  · rw [hv _ _ z J hJ, val_mul hJ, h1 z J hJ, h1' z J hJ, _root_.mul_one]
  · rw [hv _ _ z J hJ, val_mul hJ, h2 z J hJ y y', h2' z J hJ y y']

theorem triv_neg {c : Vec r →₀ ℤ} {V} (h : Triv Q D' pr c V) :
    Triv Q D' pr (-c) (fun z J y y' => (V z J y y')⁻¹) := by
  obtain ⟨Ξ, hΞ, h1, h2⟩ := h
  have hF : FormEq (fun v : c.support => (vecHom pr v.1).left) (fun v => -(c v.1))
      (fun v : (-c).support => (vecHom pr v.1).left) (fun v => (-c) v.1) := by
    intro U _ h
    rw [Finset.prod_coe_sort c.support (fun v => h (vecHom pr v).left ^ (-(c v))),
      Finset.prod_coe_sort (-c).support (fun v => h (vecHom pr v).left ^ ((-c) v)),
      Finsupp.support_neg]
    simp only [Finsupp.neg_apply]
  obtain ⟨Ξ', hΞ', hv⟩ := exists_gen Q.M.isLB hF (LB.invGen Q.M.L _ _ Ξ) (LB.isGen_invGen Q.M.L _ _ Ξ hΞ)
  refine ⟨Ξ', hΞ', fun z J hJ => ?_, fun z J hJ y y' => ?_⟩
  · rw [hv _ _ z J hJ, val_inv, h1 z J hJ, inv_one]
  · rw [hv _ _ z J hJ, val_inv, h2 z J hJ y y']

theorem zero_vecHom (hpr : ∀ i, IsMonHom (pr i)) (v : Vec r) : lift η[D'.P.A] η[D'.P.A] ≫ vecHom pr v = 1 := by
  have h : ∀ k, η[D'.P.A] ≫ pr k = 1 := fun k => by
    haveI := hpr k
    rw [IsMonHom.one_hom, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  simp only [comp_vecHom, h, one_zpow, Finset.prod_const_one, _root_.mul_one]

theorem pt_vecHom (xe : D'.X ≃+ (Fin r → Q.X)) (hc : ∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) (y y' : D'.X) (v : Vec r) :
    lift (DVR.cP D' (TK R) y) (DVR.cP D' (TK R) y') ≫ vecHom pr v = toUnit (TK R) ≫ Q.c (vecLat xe v y y') := by
  have hp : ∀ x k, DVR.cP D' (TK R) x ≫ pr k = toUnit (TK R) ≫ Q.c (xe x k) := fun x k => by
    simp only [DVR.cP, Category.assoc, hc]
  rw [comp_vecHom, vecLat, Q.c_add, PowLim.c_sum_zsmul Q, PowLim.c_sum_zsmul Q, MonObj.comp_mul,
    GlobalTheory.Mum.TensAct.comp_prod_zpow, GlobalTheory.Mum.TensAct.comp_prod_zpow]
  simp only [hp]

theorem triv_theta (xe : D'.X ≃+ (Fin r → Q.X)) (hpr : ∀ i, IsMonHom (pr i))
    (hc : ∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) (a b c : Vec r) :
    Triv Q D' pr (theta a b c) (fun z J y y' => cubV Q.cub (T := TK R) z J (toUnit (TK R) ≫ Q.c (vecLat xe a y y'))
      (toUnit (TK R) ≫ Q.c (vecLat xe b y y')) (toUnit (TK R) ≫ Q.c (vecLat xe c y y'))) := by
  have hF : FormEq (fun I => (lift (vecHom pr a) (lift (vecHom pr b) (vecHom pr c))).left ≫ thφ Q.B (x3 Q.B) I) thε
      (fun v : (theta a b c).support => (vecHom pr v.1).left) (fun v => theta a b c v.1) := fun U _ h => by
    refine (prod_cub (vecHom pr a) (vecHom pr b) (vecHom pr c) h).trans ?_
    rw [Finset.prod_coe_sort (theta a b c).support (fun v => h (vecHom pr v).left ^ theta a b c v), prod_theta,
      vecHom_add, vecHom_add, vecHom_add, vecHom_add, vecHom_zero]
  obtain ⟨Ξ, hΞ, hv⟩ := exists_gen Q.M.isLB hF
    (LB.pullGen Q.M.L (thφ Q.B (x3 Q.B)) thε Q.cub.t (lift (vecHom pr a) (lift (vecHom pr b) (vecHom pr c))).left)
    (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ Q.cub.isGen _)
  refine ⟨Ξ, hΞ, fun z J hJ => ?_, fun z J hJ y y' => ?_⟩
  · refine (hv _ _ z J hJ).trans ((val_cub Q.cub (lift η[D'.P.A] η[D'.P.A]) hJ _ _ _).trans ?_)
    rw [zero_vecHom hpr, zero_vecHom hpr, zero_vecHom hpr]
    exact (isCub_cubV Q.cub hJ).face _ _
  · refine (hv _ _ z J hJ).trans ((val_cub Q.cub (lift (DVR.cP D' (TK R) y) (DVR.cP D' (TK R) y')) hJ _ _ _).trans ?_)
    rw [pt_vecHom xe hc, pt_vecHom xe hc, pt_vecHom xe hc]

end GlobalTheory.Mum.PolTens

namespace GlobalTheory.Mum.PolTens
open GlobalTheory.TensBal

variable {R : Type} [CommRing R] [IsDomain R] {r : ℕ} {Q : Data R} {D' : DegPre R} {pr : Fin r → (D'.P.A ⟶ Q.B)}

theorem triv_congr {c : Vec r →₀ ℤ} {V V'} (h : Triv Q D' pr c V)
    (e : ∀ z J, Good Q.M.L z J → ∀ y y', V z J y y' = V' z J y y') : Triv Q D' pr c V' := by
  obtain ⟨Ξ, hΞ, h1, h2⟩ := h
  exact ⟨Ξ, hΞ, h1, fun z J hJ y y' => (h2 z J hJ y y').trans (e z J hJ y y')⟩

section TV
variable (Q) {X' : Type} [AddCommGroup X'] (xe : X' ≃+ (Fin r → Q.X))

theorem tv_add (n n' : PVec r →₀ ℤ) (z J) (y y' : X') : tv Q xe (n + n') z J y y' = tv Q xe n z J y y' * tv Q xe n' z J y y' :=
  Finsupp.prod_add_index' (fun _ => by simp only [neg_zero, zpow_zero]) (fun _ _ _ => by simp only [neg_add, zpow_add])

theorem tv_neg (n : PVec r →₀ ℤ) (z J) (y y' : X') : tv Q xe (-n) z J y y' = (tv Q xe n z J y y')⁻¹ := by
  rw [tv, tv, Finsupp.prod_neg_index (fun _ => by simp only [neg_zero, zpow_zero]), ← Finsupp.prod_inv]
  refine Finsupp.prod_congr fun p _ => ?_
  rw [neg_neg, zpow_neg, inv_inv]

theorem tv_zero (z J) (y y' : X') : tv Q xe 0 z J y y' = 1 := Finsupp.prod_zero_index

theorem tv_single (p : PVec r) (k : ℤ) (z J) (y y' : X') : tv Q xe (Finsupp.single p k) z J y y' =
    val (Q.tau (vecLat xe p.1 y y') (vecLat xe p.2 y y')) (𝟙 _) z J ^ (-k) :=
  Finsupp.prod_single_index (by simp only [neg_zero, zpow_zero])

end TV

theorem flattenMumfordBundleFormalSum_additivityRelation (u u' v : Vec r) : flat (rel1 u u' v) = theta u u' v := by
  simp only [rel1, map_sub, flat_single, lam, theta]
  abel

theorem flattenMumfordBundleFormalSum_symmetryRelation (u v : Vec r) : flat (rel2 u v) = 0 := by
  simp only [rel2, map_sub, flat_single, lam, add_comm v u]
  abel

variable (xe : D'.X ≃+ (Fin r → Q.X)) (hpr : ∀ i, IsMonHom (pr i)) (hc : ∀ z i, D'.c z ≫ pr i = Q.c (xe z i))
include hpr hc

theorem isTrivialMumfordFormalSumLattice_additivityRelation (u u' v : Vec r) : Triv Q D' pr (flat (rel1 u u' v)) (tv Q xe (rel1 u u' v)) := by
  rw [flattenMumfordBundleFormalSum_additivityRelation]
  refine triv_congr (triv_theta xe hpr hc u u' v) fun z J hJ y y' => ?_
  have e := Q.tau_add (vecLat xe u y y') (vecLat xe u' y y') (vecLat xe v y y') z J hJ
  rw [rel1, sub_eq_add_neg, sub_eq_add_neg, ← Finsupp.single_neg, ← Finsupp.single_neg, tv_add, tv_add,
    tv_single, tv_single, tv_single, vecLat_add]
  simp only [neg_neg, zpow_one, zpow_neg]
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'

theorem isTrivialMumfordFormalSumLattice_symmetryRelation (u v : Vec r) : Triv Q D' pr (flat (rel2 u v)) (tv Q xe (rel2 u v)) := by
  rw [flattenMumfordBundleFormalSum_symmetryRelation]
  refine triv_congr (triv_zero Q D' pr) fun z J hJ y y' => ?_
  rw [rel2, sub_eq_add_neg, ← Finsupp.single_neg, tv_add, tv_single, tv_single]
  simp only [neg_neg, zpow_one, zpow_neg]
  rw [Q.tau_symm _ _ z J hJ, inv_mul_cancel]

theorem triv_span {n : PVec r →₀ ℤ} (hn : n ∈ Submodule.span ℤ (rels r)) : Triv Q D' pr (flat n) (tv Q xe n) := by
  induction hn using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨p, rfl⟩ | ⟨p, rfl⟩
    · exact isTrivialMumfordFormalSumLattice_additivityRelation xe hpr hc _ _ _
    · exact isTrivialMumfordFormalSumLattice_symmetryRelation xe hpr hc _ _
  | zero =>
    rw [map_zero]
    exact triv_congr (triv_zero Q D' pr) fun z J _ y y' => (tv_zero Q xe z J y y').symm
  | add x y _ _ hx hy =>
    rw [map_add (f := _)]
    exact triv_congr (triv_add hx hy) fun z J _ a b => (tv_add Q xe x y z J a b).symm
  | smul k x _ hx =>
    have hneg : ∀ m, Triv Q D' pr (flat m) (tv Q xe m) → Triv Q D' pr (flat (-m)) (tv Q xe (-m)) := fun m hm => by
      rw [map_neg]
      exact triv_congr (triv_neg hm) fun z J _ a b => (tv_neg Q xe m z J a b).symm
    have hadd : ∀ m m', Triv Q D' pr (flat m) (tv Q xe m) → Triv Q D' pr (flat m') (tv Q xe m') →
        Triv Q D' pr (flat (m + m')) (tv Q xe (m + m')) := fun m m' hm hm' => by
      rw [map_add (f := _)]
      exact triv_congr (triv_add hm hm') fun z J _ a b => (tv_add Q xe m m' z J a b).symm
    have h0 : Triv Q D' pr (flat 0) (tv Q xe 0) := by
      rw [map_zero]
      exact triv_congr (triv_zero Q D' pr) fun z J _ y y' => (tv_zero Q xe z J y y').symm
    induction k using Int.induction_on with
    | zero => rw [zero_smul]; exact h0
    | succ j ih => rw [add_smul, one_smul]; exact hadd _ _ ih hx
    | pred j ih =>
      rw [sub_smul, one_smul, sub_eq_add_neg]
      exact hadd _ _ ih (hneg _ hx)

end GlobalTheory.Mum.PolTens

namespace GlobalTheory.Mum.PolTens
open GlobalTheory.TensBal

variable {R : Type} [CommRing R] [IsDomain R] {r : ℕ} {Q : Data R} {D' : DegPre R} {pr : Fin r → (D'.P.A ⟶ Q.B)}
  (hl : IsLimit (Fan.mk D'.P.A pr))

theorem prod_single' {G : Type} [CommGroup G] (f : Fin r → G) (i : Fin r) :
    ∏ k, f k ^ (Pi.single i (1 : ℤ) : Fin r → ℤ) k = f i := by
  rw [Fintype.prod_eq_single i (fun k hk => by rw [Pi.single_eq_of_ne hk, zpow_zero])]
  rw [Pi.single_eq_same, zpow_one]

theorem vecHom_xv (i : Fin r) : vecHom pr (xv i) = fst D'.P.A D'.P.A ≫ pr i := by
  simp only [vecHom, xv, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, _root_.mul_one]
  exact prod_single' _ i

theorem vecHom_zv (i : Fin r) : vecHom pr (zv i) = snd D'.P.A D'.P.A ≫ pr i := by
  simp only [vecHom, zv, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, _root_.one_mul]
  exact prod_single' _ i

theorem vecHom_axv (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    vecHom pr (axv A i) = fst D'.P.A D'.P.A ≫ PowLim.act pr hl A ≫ pr i := by
  simp only [vecHom, axv, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, _root_.mul_one]
  rw [PowLim.comp_act_pr]

theorem vecHom_azv (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    vecHom pr (azv A i) = snd D'.P.A D'.P.A ≫ PowLim.act pr hl A ≫ pr i := by
  simp only [vecHom, azv, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, _root_.one_mul]
  rw [PowLim.comp_act_pr]

theorem ros_pr (hpr : ∀ i, IsMonHom (pr i)) (A A' : Matrix (Fin r) (Fin r) ℤ) (a : Fin 6) :
    ∃ q : D'.P.A ⊗ D'.P.A ⟶ D'.P.A, rosatiφ D'.P.A (PowLim.act pr hl A) (PowLim.act pr hl A') a = q.left ∧
      ∀ k, q ≫ pr k = vecHom pr (rosVec A A' a k) := by
  fin_cases a
  · refine ⟨(fst D'.P.A D'.P.A ≫ PowLim.act pr hl A) * snd D'.P.A D'.P.A, rfl, fun k => ?_⟩
    show _ = vecHom pr (axv A k + zv k)
    haveI := hpr k
    rw [MonObj.mul_comp, Category.assoc, vecHom_add, vecHom_axv hl, vecHom_zv]
  · refine ⟨fst D'.P.A D'.P.A ≫ PowLim.act pr hl A, rfl, fun k => ?_⟩
    show _ = vecHom pr (axv A k)
    rw [vecHom_axv hl, Category.assoc]
  · refine ⟨snd D'.P.A D'.P.A, rfl, fun k => ?_⟩
    show _ = vecHom pr (zv k)
    rw [vecHom_zv]
  · refine ⟨fst D'.P.A D'.P.A * (snd D'.P.A D'.P.A ≫ PowLim.act pr hl A'), rfl, fun k => ?_⟩
    show _ = vecHom pr (xv k + azv A' k)
    haveI := hpr k
    rw [MonObj.mul_comp, Category.assoc, vecHom_add, vecHom_xv, vecHom_azv hl]
  · refine ⟨fst D'.P.A D'.P.A, rfl, fun k => ?_⟩
    show _ = vecHom pr (xv k)
    rw [vecHom_xv]
  · refine ⟨snd D'.P.A D'.P.A ≫ PowLim.act pr hl A', rfl, fun k => ?_⟩
    show _ = vecHom pr (azv A' k)
    rw [vecHom_azv hl, Category.assoc]

end GlobalTheory.Mum.PolTens

namespace GlobalTheory.Mum.PolTens
open GlobalTheory.TensBal

variable {R : Type} [CommRing R] [IsDomain R] {r : ℕ} {Q : Data R} {D' : DegPre R} {pr : Fin r → (D'.P.A ⟶ Q.B)}
  (hl : IsLimit (Fan.mk D'.P.A pr))

def lamV (u v : Vec r) : Fin 4 → Vec r := ![u + v, u, v, 0]

theorem ros_lam (hpr : ∀ i, IsMonHom (pr i)) (A A' : Matrix (Fin r) (Fin r) ℤ) (a : Fin 6) (i j : Fin r) (s : Fin 4) :
    rosatiφ D'.P.A (PowLim.act pr hl A) (PowLim.act pr hl A') a ≫ GlobalTheory.PolDeg.lamPts (pr i) (pr j) s =
      (vecHom pr (lamV (rosVec A A' a i) (rosVec A A' a j) s)).left := by
  obtain ⟨q, hq, hk⟩ := ros_pr hl hpr A A' a
  rw [hq]
  fin_cases s
  · show q.left ≫ (pr i * pr j).left = _
    rw [← Over.comp_left, MonObj.comp_mul, hk, hk]
    show _ = (vecHom pr (rosVec A A' a i + rosVec A A' a j)).left
    rw [vecHom_add]
  · show q.left ≫ (pr i).left = _
    rw [← Over.comp_left, hk]; rfl
  · show q.left ≫ (pr j).left = _
    rw [← Over.comp_left, hk]; rfl
  · show q.left ≫ (1 : D'.P.A ⟶ Q.B).left = _
    rw [← Over.comp_left, MonObj.comp_one]
    show _ = (vecHom pr 0).left
    rw [vecHom_zero]

theorem formEq_sig (hpr : ∀ i, IsMonHom (pr i)) (W A A' : Matrix (Fin r) (Fin r) ℤ) :
    FormEq (fun p : Fin 6 × ((Fin r × Fin r) × Fin 4) =>
        rosatiφ D'.P.A (PowLim.act pr hl A) (PowLim.act pr hl A') p.1 ≫ tensφ pr p.2)
      (fun p => rosatiε p.1 * tensε W p.2)
      (fun v : (sig W A A').support => (vecHom pr v.1).left) (fun v => sig W A A' v.1) := by
  intro U _ h
  let H : Vec r → Additive U := fun v => Additive.ofMul (h (vecHom pr v).left)
  let F : (Vec r →₀ ℤ) →+ Additive U := Finsupp.liftAddHom fun v => zmultiplesHom (Additive U) (H v)
  have hF1 : ∀ x, F (Finsupp.single x 1) = H x := fun x => by
    simp only [F, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, one_zsmul]
  have hlam : ∀ u v, F (lam u v) = ∑ s : Fin 4, Oε s • H (lamV u v s) := fun u v => by
    simp only [lam, map_add (f := _), map_sub, hF1, Fin.sum_univ_four]
    simp [Oε, lamV]
    abel
  have hR : Additive.ofMul (∏ v : (sig W A A').support, h (vecHom pr v.1).left ^ sig W A A' v.1) =
      F (sig W A A') := by
    rw [ofMul_prod]
    simp only [ofMul_zpow]
    rw [Finset.sum_coe_sort (sig W A A').support (fun v => sig W A A' v • H v)]
    simp only [F, Finsupp.liftAddHom_apply]
    rfl
  apply Additive.ofMul.injective
  rw [hR]

  simp only [ofMul_prod, ofMul_zpow, sig, map_sum, map_zsmul, hlam]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  show (rosatiε a * (W i j * Oε s)) • Additive.ofMul (h (rosatiφ D'.P.A (PowLim.act pr hl A) (PowLim.act pr hl A') a ≫
    GlobalTheory.PolDeg.lamPts (pr i) (pr j) s)) = _
  rw [ros_lam hl hpr, ← _root_.mul_assoc, mul_smul]

theorem ros_sig (hpr : ∀ i, IsMonHom (pr i)) {W : Matrix (Fin r) (Fin r) ℤ}
    (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))) (hw : w.IsGen) (A A' : Matrix (Fin r) (Fin r) ℤ)
    (u' : LB.Gen (LB.LinComb D'.P.L (rosatiφ D'.P.A (PowLim.act pr hl A) (PowLim.act pr hl A')) rosatiε)) (hu' : u'.IsGen)
    (hn' : LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ u' (zero2 D'.P.A)) (LB.oneGen D'.P.L))
    (Ξ : LB.Gen (LB.LinComb Q.M.L (fun v : (sig W A A').support => (vecHom pr v.1).left) (fun v => sig W A A' v.1)))
    (hΞ : Ξ.IsGen) (hΞ0 : ∀ (z : (𝟙_ (Over (Spec (CommRingCat.of R)))).left) J, Good Q.M.L z J → val Ξ (zero2 D'.P.A) z J = 1)
    (z : (TK R).left) (J : ((TK R).left ⟶ Q.B.left) → Q.M.L.ι) (J' : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι)
    (hJ : Good Q.M.L z J) (hJ' : Good D'.P.L z J') (y y' : D'.X) :
    (∏ a, isoV w z J J' (D'.pt2 y y' ≫ rosatiφ D'.P.A (PowLim.act pr hl A) (PowLim.act pr hl A') a) ^ rosatiε a) *
      val u' (D'.pt2 y y') z J' = val Ξ (D'.pt2 y y') z J := by
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  haveI := PowLim.act_isMonHom pr hl hpr A
  haveI := PowLim.act_isMonHom pr hl hpr A'
  have sj : Function.Surjective ((snd D'.P.A D'.P.A).left ≫ D'.P.A.hom).appTop.hom :=
    surj_comp (surj_snd hG D'.P.isAb _) (hG _ _ D'.P.isAb).2
  have he : zero2 D'.P.A ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (lift η[D'.P.A] η[D'.P.A])
  refine GlobalTheory.TensBalUniq.iso_unique Q.M.isLB D'.P.isLB w hw (formEq_sig hl hpr W A A') hu' hΞ _ (zero2 D'.P.A) he sj
    (fun s I I' hI hI' => ?_) _ (D'.pt2 y y') z J J' hJ hJ'
  have o : (η[D'.P.A] : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) = 1 := by simp [Hom.one_def]
  have p := prod_ros (PowLim.act pr hl A) (PowLim.act pr hl A') η[D'.P.A] η[D'.P.A] (fun q => isoV w s I I' q)
  rw [IsMonHom.one_hom, IsMonHom.one_hom, show η[D'.P.A] * η[D'.P.A] = η[D'.P.A] by rw [o, _root_.mul_one]] at p
  have v' := val_corr hI' hn' (𝟙 _)
  rw [val_pull hI', Category.id_comp, val_one] at v'
  rw [hΞ0 s I hI]
  refine (congrArg₂ (· * ·) p v').trans (by simp)

end GlobalTheory.Mum.PolTens

namespace GlobalTheory.Mum.PolTens
open GlobalTheory.TensBal

variable {R : Type} [CommRing R] [IsDomain R] {r : ℕ}

section Lat
variable {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (xe : X' ≃+ (Fin r → X)) (y y' : X')

theorem vecLat_xv (i : Fin r) : vecLat xe (xv i) y y' = xe y i := by
  simp [vecLat, xv, Pi.single_apply]

theorem vecLat_zv (i : Fin r) : vecLat xe (zv i) y y' = xe y' i := by
  simp [vecLat, zv, Pi.single_apply]

theorem vecLat_axv (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) : vecLat xe (axv A i) y y' = ∑ k, A i k • xe y k := by
  simp [vecLat, axv]

theorem vecLat_azv (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) : vecLat xe (azv A i) y y' = ∑ k, A i k • xe y' k := by
  simp [vecLat, azv]

end Lat

theorem tv_sigP (Q : Data R) {X' : Type} [AddCommGroup X'] (xe : X' ≃+ (Fin r → Q.X)) (W A A' : Matrix (Fin r) (Fin r) ℤ)
    (fA fA' : X' → X') (hA : ∀ y i, xe (fA y) i = ∑ j, A i j • xe y j) (hA' : ∀ y i, xe (fA' y) i = ∑ j, A' i j • xe y j)
    (z : (TK R).left) (J : ((TK R).left ⟶ Q.B.left) → Q.M.L.ι) (y y' : X') :
    tv Q xe (sigP W A A') z J y y' = ∏ a : Fin 6, (∏ i, ∏ j, val (Q.tau (xe (![fA y + y', fA y, y', y + fA' y', y, fA' y'] a) i)
      (xe (![fA y + y', fA y, y', y + fA' y', y, fA' y'] a) j)) (𝟙 _) z J ^ W i j) ^ (-(rosatiε a)) := by
  let T : (PVec r →₀ ℤ) →+ Additive ((TK R).left.presheaf.stalk z)ˣ :=
    { toFun := fun n => Additive.ofMul (tv Q xe n z J y y')
      map_zero' := by simp only [tv_zero]; rfl
      map_add' := fun n n' => by simp only [tv_add]; rfl }
  have hl : ∀ a i, vecLat xe (rosVec A A' a i) y y' = xe (![fA y + y', fA y, y', y + fA' y', y, fA' y'] a) i := by
    intro a i
    fin_cases a <;> simp [rosVec, vecLat_add, vecLat_xv, vecLat_zv, vecLat_axv, vecLat_azv, hA, hA']
  apply Additive.ofMul.injective
  change T (sigP W A A') = _

  simp only [sigP, map_sum, map_zsmul, ofMul_prod, ofMul_zpow]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show (rosatiε a * W i j) • Additive.ofMul (tv Q xe (Finsupp.single _ 1) z J y y') = _
  rw [tv_single, hl, hl, ofMul_zpow, smul_smul, smul_smul]
  congr 1
  ring

end GlobalTheory.Mum.PolTens

namespace GlobalTheory.Mum.PolTens
open GlobalTheory.TensBal

theorem axv_eq {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) : axv A i = ∑ l, A i l • xv l := by
  funext k
  rcases k with k | k
  · simp [axv, xv, Finset.sum_apply, Pi.single_apply]
  · simp [axv, xv, Finset.sum_apply]

theorem azv_eq {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) : azv A i = ∑ l, A i l • zv l := by
  funext k
  rcases k with k | k
  · simp [azv, zv, Finset.sum_apply]
  · simp [azv, zv, Finset.sum_apply, Pi.single_apply]

theorem span_sigP {r : ℕ} (W A A' : Matrix (Fin r) (Fin r) ℤ)
    (hA : A.transpose * (W + W.transpose) = (W + W.transpose) * A') : sigP W A A' ∈ Submodule.span ℤ (rels r) := by
  set N := Submodule.span ℤ (rels r)
  let F : Vec r → Vec r → (PVec r →₀ ℤ) ⧸ N := fun u v => N.mkQ (Finsupp.single (u, v) 1)
  have hF1 : ∀ u u' v, F (u + u') v = F u v + F u' v := fun u u' v => by
    have hm : rel1 u u' v ∈ N := Submodule.subset_span (Or.inl ⟨(u, u', v), rfl⟩)
    have h0 := (Submodule.Quotient.mk_eq_zero N).2 hm
    simp only [rel1] at h0
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub, sub_sub, sub_eq_zero] at h0
    exact h0
  have hF2 : ∀ u v, F u v = F v u := fun u v => by
    have hm : rel2 u v ∈ N := Submodule.subset_span (Or.inr ⟨(u, v), rfl⟩)
    have h0 := (Submodule.Quotient.mk_eq_zero N).2 hm
    simp only [rel2] at h0
    rw [Submodule.Quotient.mk_sub, sub_eq_zero] at h0
    exact h0
  have hF1' : ∀ u v v', F u (v + v') = F u v + F u v' := fun u v v' => by
    rw [hF2, hF1, hF2 v, hF2 v']
  let Fl : Vec r → Vec r →+ (PVec r →₀ ℤ) ⧸ N := fun v => AddMonoidHom.mk' (fun u => F u v) (fun u u' => hF1 u u' v)
  let Fr : Vec r → Vec r →+ (PVec r →₀ ℤ) ⧸ N := fun u => AddMonoidHom.mk' (fun v => F u v) (fun v v' => hF1' u v v')
  have hsumL : ∀ (c : Fin r → ℤ) (s : Fin r → Vec r) v, F (∑ l, c l • s l) v = ∑ l, c l • F (s l) v := fun c s v => by
    have := map_sum (Fl v) (fun l => c l • s l) Finset.univ
    simp only [map_zsmul] at this
    exact this
  have hsumR : ∀ (c : Fin r → ℤ) (s : Fin r → Vec r) u, F u (∑ l, c l • s l) = ∑ l, c l • F u (s l) := fun c s u => by
    have := map_sum (Fr u) (fun l => c l • s l) Finset.univ
    simp only [map_zsmul] at this
    exact this
  let X : (Fin r → Vec r) → (Fin r → Vec r) → (PVec r →₀ ℤ) ⧸ N := fun s t => ∑ i, ∑ j, W i j • F (s i) (t j)
  let Bf : (Fin r → Vec r) → (Fin r → Vec r) → (PVec r →₀ ℤ) ⧸ N :=
    fun s t => ∑ i, ∑ j, (W + W.transpose) i j • F (s i) (t j)
  have expand : ∀ s t : Fin r → Vec r, X (fun i => s i + t i) (fun i => s i + t i) = X s s + X t t + Bf s t := by
    intro s t
    have hc : ∑ i, ∑ j, W i j • F (t i) (s j) = ∑ i, ∑ j, W.transpose i j • F (s i) (t j) := by
      rw [Finset.sum_comm]
      simp only [Matrix.transpose_apply, hF2 (t _)]
    simp only [X, Bf, hF1, hF1', smul_add, Finset.sum_add_distrib, Matrix.add_apply, add_smul]
    rw [hc]
    abel
  have hπ : N.mkQ (sigP W A A') = ∑ a : Fin 6, rosatiε a • X (rosVec A A' a) (rosVec A A' a) := by

    simp only [sigP, map_sum, map_zsmul, X, Finset.smul_sum, mul_smul]
    rfl
  have e0 : rosVec A A' 0 = fun i => axv A i + zv i := rfl
  have e1 : rosVec A A' 1 = fun i => axv A i := rfl
  have e2 : rosVec A A' 2 = fun i => zv i := rfl
  have e3 : rosVec A A' 3 = fun i => xv i + azv A' i := rfl
  have e4 : rosVec A A' 4 = fun i => xv i := rfl
  have e5 : rosVec A A' 5 = fun i => azv A' i := rfl
  have ε0 : rosatiε 0 = 1 := rfl
  have ε1 : rosatiε 1 = -1 := rfl
  have ε2 : rosatiε 2 = -1 := rfl
  have ε3 : rosatiε 3 = -1 := rfl
  have ε4 : rosatiε 4 = 1 := rfl
  have ε5 : rosatiε 5 = 1 := rfl
  have L : Bf (fun i => axv A i) (fun i => zv i) =
      ∑ l, ∑ j, (A.transpose * (W + W.transpose)) l j • F (xv l) (zv j) := by
    simp only [Bf, axv_eq, hsumL, Finset.smul_sum, smul_smul, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_smul]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  have Rr : Bf (fun i => xv i) (fun i => azv A' i) =
      ∑ i, ∑ m, ((W + W.transpose) * A') i m • F (xv i) (zv m) := by
    simp only [Bf, azv_eq, hsumR, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  have hB : Bf (fun i => axv A i) (fun i => zv i) = Bf (fun i => xv i) (fun i => azv A' i) := by
    rw [L, Rr, hA]
  rw [← Submodule.Quotient.mk_eq_zero N]
  change N.mkQ (sigP W A A') = 0
  rw [hπ, Fin.sum_univ_six, ε0, ε1, ε2, ε3, ε4, ε5, e0, e1, e2, e3, e4, e5, expand, expand, hB]
  simp only [one_smul, neg_smul]
  abel

end GlobalTheory.Mum.PolTens

namespace GlobalTheory.Mum.PolTens
open GlobalTheory.TensBal

theorem transpose_mul_eq {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det)
    (a : TensO (symUnitOf W h)) :
    (TensO.mat _ a).transpose * (W + W.transpose) = (W + W.transpose) * TensO.mat _ (star a) := by
  have hb : ((symUnitOf W h).1 : Matrix (Fin r) (Fin r) ℤ) = W + W.transpose := rfl
  rw [TensO.star_def]
  show _ = (W + W.transpose) * (((((symUnitOf W h).1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
    (TensO.mat _ a).transpose * ((symUnitOf W h).1 : Matrix (Fin r) (Fin r) ℤ)))
  rw [hb.symm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

variable {R : Type} [CommRing R] [IsDomain R] {r : ℕ} {Q : Data R} {D' : DegPre R} {pr : Fin r → (D'.P.A ⟶ Q.B)}

theorem tau_pol {W : Matrix (Fin r) (Fin r) ℤ} (xe : D'.X ≃+ (Fin r → Q.X))
    (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W)))
    (hpsi : ∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' →
      val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j)
    {z : (TK R).left} {J J'} (hJ : Good Q.M.L z J) (hJ' : Good D'.P.L z J') (p q : D'.X) :
    val (D'.tau p q) (𝟙 _) z J' =
      isoV w z J J' (DVR.cP D' (TK R) (p + q)).left * (∏ i, ∏ j, val (Q.tau (xe (p + q) i) (xe (p + q) j)) (𝟙 _) z J ^ W i j) *
      (isoV w z J J' (DVR.cP D' (TK R) p).left * ∏ i, ∏ j, val (Q.tau (xe p i) (xe p j)) (𝟙 _) z J ^ W i j)⁻¹ *
      (isoV w z J J' (DVR.cP D' (TK R) q).left * ∏ i, ∏ j, val (Q.tau (xe q i) (xe q j)) (𝟙 _) z J ^ W i j)⁻¹ *
      (val D'.rigK (𝟙 _) z J')⁻¹ := by
  rw [GlobalTheory.TauBalBox.tau_val D' hJ', hpsi _ z J J' hJ hJ', hpsi _ z J J' hJ hJ', hpsi _ z J J' hJ hJ']
  rfl

end GlobalTheory.Mum.PolTens
end -- clump:auto
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTrivialMumfordFormalSumLatticeAdditivityRelati =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPeriodsBalancedIntegralMatrices =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPeriodsBalancedIntegralMatrices", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgIdemBinv\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTrivialMumfordFormalSumLatticeAdditivityRelati\nimport Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal\nimport Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

open GlobalTheory.Mum.PolTens GlobalTheory.TensBal in
theorem GlobalTheory.Mum.PolTens.tauBal_polTens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegData R (maximalIdeal R))
    {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef →
    ∀ (pr : Fin r → (D'.toPre.P.A ⟶ Q.B)) (hl : IsLimit (Fan.mk D'.toPre.P.A pr)) (xe : D'.toPre.X ≃+ (Fin r → Q.X))
    (w : LB.Iso D'.toPre.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))),
    (∀ i, IsMonHom (pr i)) → (∀ z i, D'.toPre.c z ≫ pr i = Q.c (xe z i)) → w.IsGen →
    (∀ y z J J', Good Q.M.L z J → Good D'.toPre.P.L z J' →
      val (D'.toPre.psi y) (𝟙 _) z J' = gm (D'.toPre.xK y) z _ (w.s (fun k => J (D'.toPre.xK y ≫ tensφ pr k), J' (D'.toPre.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) →
    letI := PowLim.mod xe (symUnitOf W h)
    ∀ a : TensO (symUnitOf W h), D'.toPre.TauBal (PowLim.act pr hl (TensO.mat _ a)) (PowLim.act pr hl (TensO.mat _ (star a)))
      (fun y => a • y) (fun y => star a • y) := by
  intro R _ _ _ _ Q D' r W h _ pr hl xe w hpr hc hw hpsi
  letI := PowLim.mod xe (symUnitOf W h)
  intro a
  have hA := transpose_mul_eq W h a
  intro u' hu' hn' y y'
  have htr := triv_span xe hpr hc (span_sigP W _ _ hA)
  rw [flat_sigP] at htr
  obtain ⟨Ξ, hΞ, hΞ0, hΞv⟩ := htr
  refine corr_of_val D'.toPre.P.isLB fun z J' hJ' => ?_
  obtain ⟨J, hJ⟩ := GlobalTheory.BoxFamily.exists_good_at Q.M.isLB z
  have key := ros_sig hl hpr w hw _ _ u' hu' hn' Ξ hΞ hΞ0 z J J' hJ hJ' y y'
  rw [hΞv z J hJ y y', tv_sigP Q xe W _ _ (fun y => a • y) (fun y => star a • y) (PowLim.xe_smul xe _ a)
    (PowLim.xe_smul xe _ (star a)) z J y y'] at key
  have prr := prod_ros (PowLim.act pr hl (TensO.mat _ a)) (PowLim.act pr hl (TensO.mat _ (star a)))
    (DVR.cP D'.toPre (TK R) y) (DVR.cP D'.toPre (TK R) y') (isoV w z J J')
  have l₁ : DVR.cP D'.toPre (TK R) y ≫ PowLim.act pr hl (TensO.mat _ a) = DVR.cP D'.toPre (TK R) (a • y) := by
    rw [DVR.cP, DVR.cP, PowLim.c_smul Q D'.toPre pr hl xe hc, Category.assoc]
  have l₂ : DVR.cP D'.toPre (TK R) y' ≫ PowLim.act pr hl (TensO.mat _ (star a)) =
      DVR.cP D'.toPre (TK R) (star a • y') := by
    rw [DVR.cP, DVR.cP, PowLim.c_smul Q D'.toPre pr hl xe hc, Category.assoc]
  rw [l₁, l₂, ← DVR.cPoint_add, ← DVR.cPoint_add] at prr
  change ∏ k, isoV w z J J' (D'.toPre.pt2 y y' ≫ rosatiφ D'.toPre.P.A (PowLim.act pr hl (TensO.mat _ a))
    (PowLim.act pr hl (TensO.mat _ (star a))) k) ^ rosatiε k = _ at prr
  rw [prr] at key
  rw [val_mul hJ', val_pull hJ', Category.id_comp, tau_pol xe w hpsi hJ hJ', tau_pol xe w hpsi hJ hJ']
  have e0 : rosatiε 0 = 1 := rfl
  have e1 : rosatiε 1 = -1 := rfl
  have e2 : rosatiε 2 = -1 := rfl
  have e3 : rosatiε 3 = -1 := rfl
  have e4 : rosatiε 4 = 1 := rfl
  have e5 : rosatiε 5 = 1 := rfl
  have v0 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 0 = a • y + y' := rfl
  have v1 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 1 = a • y := rfl
  have v2 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 2 = y' := rfl
  have v3 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 3 = y + star a • y' := rfl
  have v4 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 4 = y := rfl
  have v5 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 5 = star a • y' := rfl
  rw [Fin.prod_univ_six] at key
  erw [v0, v1, v2, v3, v4, v5] at key
  simp only [e0, e1, e2, e3, e4, e5] at key
  apply Additive.ofMul.injective
  have k' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at k' ⊢
  linear_combination (norm := abel) k'
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPeriodsBalancedIntegralMatrices =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPeriodsBalancedIntegralMatricesStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPeriodsBalancedIntegralMatricesStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgIdemBinv\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPeriodsBalancedIntegralMatrices\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPeriodsBalancedIntegralMatricesStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyOfTensorDataPosDefUnimodular =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyOfTensorDataPosDefUnimodular", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgIdemBinv\npublic import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordIsoPeriodsFactorTensorPolarisedStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjMumfordTensorPowerOfPosDef\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPeriodsBalancedIntegralMatricesStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum.PowLim.Rosati

open GlobalTheory.CechPic GlobalTheory.Mum.RosatiTens

variable {R : Type} [CommRing R] [IsDomain R] {Q : Data R} {D' : DegPre R} {r : ℕ}
  {pr : Fin r → (D'.P.A ⟶ Q.B)}

def pairQ (Q : Data R) (pr : Fin r → (D'.P.A ⟶ Q.B)) (M : Matrix (Fin r) (Fin r) ℤ) {X : Over (Spec (CommRingCat.of R))}
    (u v : X ⟶ D'.P.A) : Pic X.left :=
  ∑ i, ∑ j, M i j • lam (cls Q.M.L Q.M.isLB) (u ≫ pr i) (v ≫ pr j)

theorem cls_pow {W : Matrix (Fin r) (Fin r) ℤ} (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W)))
    (hw : w.IsGen) : cls D'.P.L D'.P.isLB = ∑ i, ∑ j, W i j • lam (cls Q.M.L Q.M.isLB) (pr i) (pr j) := by
  have hC := LB.isLB_linComb Q.M.isLB (tensφ pr) (tensε W)
  refine ((cls_eq_iff D'.P.isLB hC).2 ⟨w, hw⟩).trans ?_
  rw [cls_linComb Q.M.isLB, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Fin.sum_univ_four, tensφ, tensε, GlobalTheory.PolDeg.lamPts, Oε, lam, mul_smul, ← smul_add]
  congr 1
  simp
  abel

theorem pull_pow {W : Matrix (Fin r) (Fin r) ℤ} (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W)))
    (hw : w.IsGen) {X : Over (Spec (CommRingCat.of R))} (h : X ⟶ D'.P.A) :
    pull h.left (cls D'.P.L D'.P.isLB) = pairQ Q pr W h h := by

  rw [cls_pow w hw, pairQ, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_

  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, pull_lam]

theorem pairQ_mul (hpr : ∀ i, IsMonHom (pr i)) (W : Matrix (Fin r) (Fin r) ℤ) {X : Over (Spec (CommRingCat.of R))}
    (u v : X ⟶ D'.P.A) :
    pairQ Q pr W (u * v) (u * v) = pairQ Q pr W u u + pairQ Q pr W v v + pairQ Q pr (W + W.transpose) u v := by
  have hm : ∀ i, (u * v) ≫ pr i = u ≫ pr i * v ≫ pr i := fun i => by
    haveI := hpr i
    exact MonObj.mul_comp _ _ _
  have hΘ : ∃ t : LB.Gen (Theta Q.B Q.M.L), t.IsGen := ⟨Q.cub.t, Q.cub.isGen⟩
  have e : ∑ i, ∑ j, W i j • lam (cls Q.M.L Q.M.isLB) (v ≫ pr i) (u ≫ pr j) =
      ∑ i, ∑ j, W.transpose i j • lam (cls Q.M.L Q.M.isLB) (u ≫ pr i) (v ≫ pr j) := by
    rw [Finset.sum_comm]
    simp only [Matrix.transpose_apply, lam_comm _ (v ≫ _)]
  simp only [pairQ, hm, lam_mul_left Q.M.isLB hΘ, lam_mul_right Q.M.isLB hΘ, smul_add, Finset.sum_add_distrib,
    Matrix.add_apply, add_smul]
  rw [e]
  abel

theorem comp_act_pr' (hl : IsLimit (Fan.mk D'.P.A pr)) {X : Over (Spec (CommRingCat.of R))} (u : X ⟶ D'.P.A)
    (m : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    (u ≫ PowLim.act pr hl m) ≫ pr i = ∏ k, (u ≫ pr k) ^ m i k := by
  rw [Category.assoc, PowLim.act_pr]
  exact (map_prod (pre (Z := Q.B) u) _ _).trans (Finset.prod_congr rfl fun k _ => map_zpow (pre (Z := Q.B) u) _ _)

theorem pairQ_act_left (hl : IsLimit (Fan.mk D'.P.A pr)) (M m : Matrix (Fin r) (Fin r) ℤ)
    {X : Over (Spec (CommRingCat.of R))} (u v : X ⟶ D'.P.A) :
    pairQ Q pr M (u ≫ PowLim.act pr hl m) v = pairQ Q pr (m.transpose * M) u v := by
  have hΘ : ∃ t : LB.Gen (Theta Q.B Q.M.L), t.IsGen := ⟨Q.cub.t, Q.cub.isGen⟩
  simp only [pairQ, comp_act_pr', lam_prod_left Q.M.isLB hΘ, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem pairQ_act_right (hl : IsLimit (Fan.mk D'.P.A pr)) (M m : Matrix (Fin r) (Fin r) ℤ)
    {X : Over (Spec (CommRingCat.of R))} (u v : X ⟶ D'.P.A) :
    pairQ Q pr M u (v ≫ PowLim.act pr hl m) = pairQ Q pr (M * m) u v := by
  have hΘ : ∃ t : LB.Gen (Theta Q.B Q.M.L), t.IsGen := ⟨Q.cub.t, Q.cub.isGen⟩
  simp only [pairQ, comp_act_pr', lam_prod_right Q.M.isLB hΘ, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

theorem rosatiAdj_pow : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (h : IsUnit (W + W.transpose).det) (pr : Fin r → (D'.P.A ⟶ Q.B)) (hl : IsLimit (Fan.mk D'.P.A pr))
    (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), (∀ i, IsMonHom (pr i)) → w.IsGen →
    ∀ a : TensO (symUnitOf W h), RosatiAdj D'.P.A D'.P.L (PowLim.act pr hl (TensO.mat _ a)) (PowLim.act pr hl (TensO.mat _ (star a))) := by
  intro R _ _ Q D' r W h pr hl w hpr hw a
  intro s
  refine ⟨⊤, trivial, (cls_eq_zero_iff (LB.isLB_linComb D'.P.isLB _ _)).1 ?_⟩
  rw [cls_linComb D'.P.isLB]
  let f := PowLim.act pr hl (TensO.mat _ a)
  let g := PowLim.act pr hl (TensO.mat _ (star a))
  let H : Fin 6 → (D'.P.A ⊗ D'.P.A ⟶ D'.P.A) := ![fst _ _ ≫ f * snd _ _, fst _ _ ≫ f, snd _ _,
    fst _ _ * snd _ _ ≫ g, fst _ _, snd _ _ ≫ g]
  have hH : rosatiφ D'.P.A f g = fun k => (H k).left := by
    funext k
    fin_cases k <;> simp [rosatiφ, H, padd, Hom.mul_def]
  have key : ∑ k, rosatiε k • pull (rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB) = 0 := by
    simp only [hH, pull_pow w hw]
    simp only [Fin.sum_univ_six, H, rosatiε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val]
    rw [pairQ_mul hpr, pairQ_mul hpr]
    rw [pairQ_act_left hl (W + W.transpose) (TensO.mat _ a) (fst _ _) (snd _ _),
      pairQ_act_right hl (W + W.transpose) (TensO.mat _ (star a)) (fst _ _) (snd _ _), symUnit_mul_star]
    simp only [one_smul, neg_smul]
    abel
  calc ∑ k, rosatiε k • pull (((D'.P.A ⊗ D'.P.A).hom ⁻¹ᵁ ⊤).ι ≫ rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB)
      = pull (((D'.P.A ⊗ D'.P.A).hom ⁻¹ᵁ ⊤).ι)
          (∑ k, rosatiε k • pull (rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB)) := by

        simp only [pull_comp, map_sum, map_zsmul]
    _ = 0 := by rw [key, map_zero]

end GlobalTheory.Mum.PowLim.Rosati

theorem GlobalTheory.Mum.PFactor.nonempty_of_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegData R (maximalIdeal R))
  {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → 1 ≤ r →
  ∀ (pr : Fin r → (D'.toPre.P.A ⟶ Q.B)) (xe : D'.toPre.X ≃+ (Fin r → Q.X))
    (w : LB.Iso D'.toPre.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))),
    (∀ i, IsMonHom (pr i)) → Nonempty (IsLimit (Fan.mk D'.toPre.P.A pr)) →
    (∀ z i, D'.toPre.c z ≫ pr i = Q.c (xe z i)) → w.IsGen →
    (∀ y z J J', Good Q.M.L z J → Good D'.toPre.P.L z J' →
      val (D'.toPre.psi y) (𝟙 _) z J' = gm (D'.toPre.xK y) z _ (w.s (fun k => J (D'.toPre.xK y ≫ tensφ pr k), J' (D'.toPre.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) →
    Nonempty (PFactor Q D'.toPre) := by
  intro R _ _ _ hR Q D' r W hpos hdet hr pr xe w hpr hlim hc hw hpsi
  let hl := hlim.some
  let s := symUnitOf W hdet
  let i₀ : Fin r := ⟨0, hr⟩
  letI := PowLim.mod xe s
  obtain ⟨w', hw', htau⟩ := _root_.GlobalTheory.Mum.PolPair.pairing_factor R hR Q D' W hdet hpos pr hl xe w hpr hc hw hpsi i₀
  obtain ⟨hxx, hxe, hinj, honto⟩ := PowLim.factor_latt xe s i₀
  have hp : 0 < (s.1 : Matrix (Fin r) (Fin r) ℤ) i₀ i₀ := by
    have h := hpos.diag_pos (i := i₀)
    have h' : (0 : ℝ) < (((W + W.transpose) i₀ i₀ : ℤ) : ℝ) := h
    exact_mod_cast h'
  exact ⟨{
    O := TensO s
    mod := PowLim.mod xe s
    o := { onB := { act := fun a => PowLim.act pr hl (TensO.mat s a)
                    hom := fun a => PowLim.act_isMonHom pr hl hpr _
                    map_one := PowLim.act_one pr hl
                    map_mul := fun a b => PowLim.act_mul pr hl _ _
                    map_add := fun a b => PowLim.act_add pr hl hpr _ _
                    rosati := GlobalTheory.Mum.PowLim.Rosati.rosatiAdj_pow R Q D'.toPre W hdet pr hl w hpr hw }
           c_lin := PowLim.c_smul Q D'.toPre pr hl xe hc s
           tau_bal := _root_.GlobalTheory.Mum.PolTens.tauBal_polTens R hR Q D' W hdet hpos pr hl xe w hpr hc hw hpsi }
    e := TensO.idem s i₀
    f := TensO.binv s
    inc := PowLim.inc pr hl i₀
    pr := pr i₀
    xi := PowLim.xi xe i₀
    xp := PowLim.xp xe i₀
    w := w'
    idem := TensO.idem_mul_idem s i₀
    inc_hom := PowLim.inc_isMonHom pr hl hpr i₀
    pr_hom := hpr i₀
    inc_pr := PowLim.inc_pr_self pr hl i₀
    pr_inc := PowLim.pr_inc pr hl i₀
    xp_xi := hxx
    xi_xp := hxe
    c_xi := PowLim.c_xi Q D'.toPre pr hl xe hc i₀
    inj := hinj
    onto := honto
    w_gen := hw'
    tau := htau
    alg := PowLim.alg_idem_binv s i₀ hp }⟩
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyOfTensorDataPosDefUnimodular =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyOfTensorDataPosDefUnimodularStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyOfTensorDataPosDefUnimodularStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyOfTensorDataPosDefUnimodular\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.nonempty_of_tensorData_posDef_unimodular : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegData R (maximalIdeal R))
  {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → 1 ≤ r →
  ∀ (pr : Fin r → (D'.toPre.P.A ⟶ Q.B)) (xe : D'.toPre.X ≃+ (Fin r → Q.X))
    (w : LB.Iso D'.toPre.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))),
    (∀ i, IsMonHom (pr i)) → Nonempty (IsLimit (Fan.mk D'.toPre.P.A pr)) →
    (∀ z i, D'.toPre.c z ≫ pr i = Q.c (xe z i)) → w.IsGen →
    (∀ y z J J', Good Q.M.L z J → Good D'.toPre.P.L z J' →
      val (D'.toPre.psi y) (𝟙 _) z J' = gm (D'.toPre.xK y) z _ (w.s (fun k => J (D'.toPre.xK y ≫ tensφ pr k), J' (D'.toPre.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) →
    Nonempty (PFactor Q D'.toPre) := by
  first | exact @GlobalTheory.Mum.PFactor.nonempty_of_tens
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyOfTensorDataPosDefUnimodularStatement =====
