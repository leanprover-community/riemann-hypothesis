import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteMonomialsWithPrescribedPlaceDegree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAlgebraicIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralRealPointUnitScalarSinglePlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PowExpIOrInvInjective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactCommutingCartanInvolutionMovedStandard
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapDomainFstEqOfCoeffMatrixFamilyBilateralSubsti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffMatrixFamilyBilateralSubstitutionMonomialCo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixFamilyBilateralSubstitutionCompEqMul
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactUnitaryRealPointsOfGramEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomWeilActionFockPureTensorSubstituti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanCharacterThetaStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.RealAvg

open MvPolynomial

theorem mapDomain_fst_apply {ι κ : Type} [DecidableEq ι] (k : ι × κ →₀ ℕ) (τ : ι) :
    Finsupp.mapDomain Prod.fst k τ = ∑ v ∈ k.support with v.1 = τ, k v := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finsupp.single_apply]

def Mon (D : D7) (m n : ℕ) (d : D.what₂.Tau →₀ ℕ) : Set (FVar D m n →₀ ℕ) := {k | Finsupp.mapDomain Prod.fst k = d}

open Classical in
theorem mon_finite (D : D7) (m n : ℕ) (d : D.what₂.Tau →₀ ℕ) : (Mon D m n d).Finite :=
  (GlobalTheory.finite_monomials_of_placeDegree D m n (fun τ => d τ)).subset fun k hk τ => by
    have e := mapDomain_fst_apply k τ
    rw [show Finsupp.mapDomain Prod.fst k = d from hk] at e
    convert e.symm

noncomputable instance (D : D7) (m n : ℕ) (d : D.what₂.Tau →₀ ℕ) : Fintype (Mon D m n d) := (mon_finite D m n d).fintype

variable {D : D7}

def substMat (θ : InfFam D) (V : HSp D) (m : ℕ) (d : D.what₂.Tau →₀ ℕ) (g : GA D V) :
    Matrix (Mon D m V.rank d) (Mon D m V.rank d) ℂ :=
  fun k' k => coeff k'.1 (GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ))
    (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g)) (monomial k.1 1))

open MvPolynomial

theorem substF_one {ι : Type} {N n : ℕ} (P : MvPolynomial (ι × Fin N × Fin n) ℂ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) P = P := by
  have key : GlobalTheory.CompactHowe.substF (ι := ι) (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ))
      (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) = AlgHom.id ℂ _ := by
    refine algHom_ext fun p => ?_
    rw [GlobalTheory.CompactHowe.substF_X, Finset.sum_eq_single p.2.1, Finset.sum_eq_single p.2.2]
    · simp
    · intro l _ hl; simp [Matrix.one_apply_ne hl]
    · simp
    · intro k _ hk; simp [Matrix.one_apply_ne hk]
    · simp
  rw [key]; rfl

theorem eq_sum_mon {D : D7} {m n : ℕ} {d : D.what₂.Tau →₀ ℕ} (P : MvPolynomial (FVar D m n) ℂ)
    (hP : ∀ k', coeff k' P ≠ 0 → k' ∈ Mon D m n d) :
    P = ∑ k : Mon D m n d, coeff k.1 P • monomial k.1 (1 : ℂ) := by
  classical
  ext k'
  rw [coeff_sum]
  simp only [coeff_smul, coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hk : k' ∈ Mon D m n d
  · rw [Finset.sum_eq_single ⟨k', hk⟩]
    · simp
    · intro b _ hb; rw [if_neg]; intro h; exact hb (Subtype.ext h)
    · simp
  · rw [Finset.sum_eq_zero]
    · by_contra h; exact hk (hP k' h)
    · intro b _; rw [if_neg]; rintro rfl; exact hk b.2

variable {D : D7}

theorem substMat_one (θ : InfFam D) (V : HSp D) (m : ℕ) (d : D.what₂.Tau →₀ ℕ) : substMat θ V m d 1 = 1 := by
  classical
  ext k' k
  simp only [substMat, GlobalTheory.StdUnn.CartanMove.compAt_mt_one, substF_one, coeff_monomial, Matrix.one_apply]
  by_cases h : k' = k
  · subst h; simp
  · have h' : (k.1 : FVar D m V.rank →₀ ℕ) ≠ k'.1 := fun e => h (Subtype.ext e.symm)
    simp [h, h']

theorem one_alg (m : ℕ) (i : D.what₂.Tau) (a b : Fin m) :
    IsAlgebraic ℚ ((fun _ : D.what₂.Tau => (1 : Matrix (Fin m) (Fin m) ℂ)) i a b) := by
  by_cases hab : a = b
  · subst hab; show IsAlgebraic ℚ ((1 : Matrix (Fin m) (Fin m) ℂ) a a); rw [Matrix.one_apply_eq]; exact isAlgebraic_one
  · show IsAlgebraic ℚ ((1 : Matrix (Fin m) (Fin m) ℂ) a b); rw [Matrix.one_apply_ne hab]; exact isAlgebraic_zero

section Avg

variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (κ : Measure K) [IsProbabilityMeasure κ] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Group K] [IsTopologicalGroup K] [DecidableEq ι] in
theorem integral_expand (ρ : K → Matrix ι ι ℂ) (hρ : Continuous ρ) (Φ : ι → ℂ) (F : K → ℂ) (k : ι)
    (hF : ∀ g, F g = ∑ k', ρ g k' k * Φ k') : ∫ g, F g ∂κ = ∑ k', (∫ g, ρ g k' k ∂κ) * Φ k' := by
  simp_rw [hF]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun k' _ => integral_mul_const _ _
  · exact fun k' _ => (GlobalTheory.HaarAlg.integrable_of_continuous κ (hρ.matrix_elem k' k)).mul_const _

theorem integral_eq_zero_of_scalar [κ.IsMulLeftInvariant] (ρ : K →* Matrix ι ι ℂ) (hρ : Continuous ρ) (z : K) (c : ℂ)
    (hc : c ≠ 1) (hz : ρ z = c • 1) (a b : ι) : ∫ g, ρ g a b ∂κ = 0 := by
  classical
  have h := GlobalTheory.HaarAlg.rho_mul_avg κ ρ hρ z
  rw [hz, Matrix.smul_mul, Matrix.one_mul] at h
  have h3 := congrFun (congrFun h a) b
  simp only [Matrix.smul_apply, smul_eq_mul, GlobalTheory.HaarAlg.avg, Matrix.of_apply] at h3
  have h2 : (c - 1) * ∫ g, ρ g a b ∂κ = 0 := by rw [sub_mul, one_mul, h3, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hc)

end Avg

end GlobalTheory.RealAvg
end
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mapDomain_fst_eq_of_coeff_matrixFamilyBilateralSubstitution_ne_zero : ∀ {ι : Type} {N n : ℕ} (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ) (k k' : ι × Fin N × Fin n →₀ ℕ), MvPolynomial.coeff k' (GlobalTheory.CompactHowe.substF h g (MvPolynomial.monomial k 1)) ≠ 0 → Finsupp.mapDomain Prod.fst k' = Finsupp.mapDomain Prod.fst k := by
  first | exact @GlobalTheory.CompactHowe.mapDomain_fst_eq_of_coeff_substF_ne_zero | exact GlobalTheory.CompactHowe.mapDomain_fst_eq_of_coeff_substF_ne_zero | (intros; apply GlobalTheory.CompactHowe.mapDomain_fst_eq_of_coeff_substF_ne_zero <;> assumption)
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_matrixFamilyBilateralSubstitution_monomial_continuous_algebraic : ∀ {ι : Type} {N n : ℕ} (k k' : ι × Fin N × Fin n →₀ ℕ), Continuous (fun p : (ι → Matrix (Fin N) (Fin N) ℂ) × (ι → Matrix (Fin n) (Fin n) ℂ) => MvPolynomial.coeff k' (GlobalTheory.CompactHowe.substF p.1 p.2 (MvPolynomial.monomial k 1))) ∧ ∀ (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ), (∀ i a b, IsAlgebraic ℚ (h i a b)) → (∀ i a b, IsAlgebraic ℚ (g i a b)) → IsAlgebraic ℚ (MvPolynomial.coeff k' (GlobalTheory.CompactHowe.substF h g (MvPolynomial.monomial k 1))) := by
  first | exact @GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic | exact GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic | (intros; apply GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic <;> assumption)
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixFamilyBilateralSubstitution_comp_eq_mul : ∀ {ι : Type} {N n : ℕ} (h h' : ι → Matrix (Fin N) (Fin N) ℂ) (g g' : ι → Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (ι × Fin N × Fin n) ℂ), GlobalTheory.CompactHowe.substF h g (GlobalTheory.CompactHowe.substF h' g' P) = GlobalTheory.CompactHowe.substF (h * h') (g * g') P := by
  first | exact @GlobalTheory.CompactHowe.substF_mul | exact GlobalTheory.CompactHowe.substF_mul | (intros; apply GlobalTheory.CompactHowe.substF_mul <;> assumption)
end

section
section
noncomputable section
open MvPolynomial

namespace GlobalTheory.CompactHowe

theorem substF_scalar_X {ι : Type} [DecidableEq ι] {N n : ℕ} (τ₀ : ι) (ζ : ℂ) (p : ι × Fin N × Fin n) :
    substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun τ => if τ = τ₀ then ζ • (1 : Matrix (Fin n) (Fin n) ℂ) else 1) (X p)
      = C (if p.1 = τ₀ then ζ else 1) * X p := by
  rw [substF_X, Finset.sum_eq_single p.2.1, Finset.sum_eq_single p.2.2]
  · obtain ⟨a, b⟩ := p
    by_cases h : a = τ₀
    · subst h; simp
    · simp [h]
  · intro l _ hl
    by_cases h : p.1 = τ₀ <;> simp [h, Matrix.one_apply_ne hl]
  · simp
  · intro k _ hk
    simp [Matrix.one_apply_ne hk]
  · simp

theorem mapDomain_fst_apply {ι : Type} [DecidableEq ι] {N n : ℕ} (k : ι × Fin N × Fin n →₀ ℕ) (τ₀ : ι) :
    Finsupp.mapDomain Prod.fst k τ₀ = ∑ p ∈ k.support, if p.1 = τ₀ then k p else 0 := by
  unfold Finsupp.mapDomain
  rw [Finsupp.sum_apply]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun p _ => ?_
  dsimp only
  rw [Finsupp.single_apply]

theorem substF_scalar_monomial {ι : Type} [DecidableEq ι] {N n : ℕ} (τ₀ : ι) (ζ : ℂ) (k : ι × Fin N × Fin n →₀ ℕ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun τ => if τ = τ₀ then ζ • (1 : Matrix (Fin n) (Fin n) ℂ) else 1) (MvPolynomial.monomial k 1) = ζ ^ (Finsupp.mapDomain Prod.fst k τ₀) • MvPolynomial.monomial k 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod, map_prod]
  simp only [map_pow, substF_scalar_X, mul_pow, Finset.prod_mul_distrib]
  rw [mapDomain_fst_apply, smul_eq_C_mul, ← Finset.prod_pow_eq_pow_sum, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← map_pow]
  split_ifs <;> simp

end GlobalTheory.CompactHowe
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixFamilyBilateralSubstitution_scalar_monomial : ∀ {ι : Type} [DecidableEq ι] {N n : ℕ} (τ₀ : ι) (ζ : ℂ) (k : ι × Fin N × Fin n →₀ ℕ), GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun τ => if τ = τ₀ then ζ • (1 : Matrix (Fin n) (Fin n) ℂ) else 1) (MvPolynomial.monomial k 1) = ζ ^ (Finsupp.mapDomain Prod.fst k τ₀) • MvPolynomial.monomial k 1 := by
  atlas_forward_decl GlobalTheory.CompactHowe.substF_scalar_monomial
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_unitaryRealPoints_of_gram_eq_one : ∀ (D : D7) (V : HSp D), V.gram = 1 → IsCompact (GinfC V : Set (GA D V)) := by
  first | exact @GlobalTheory.GramOneCompact.isCompact_GinfC_of_gram_eq_one | exact GlobalTheory.GramOneCompact.isCompact_GinfC_of_gram_eq_one | (intros; apply GlobalTheory.GramOneCompact.isCompact_GinfC_of_gram_eq_one <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.RealAlgDense

theorem dense_alg : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ V : HSp D, Dense {g : GinfC V | ∀ τ a b, IsAlgebraic ℚ (compAt θ τ (Formalism.L2.Theta.mt V g.1) a b)} := by
  intro D θ hθ V
  obtain ⟨e, he⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  have hfin : ∀ h : GA D V, h ∈ GinfC V ↔ (e h).2 = 1 := fun h =>
    ⟨fun H => Subtype.ext (Units.ext ((he h).1.trans (congrArg Units.val (MonoidHom.mem_ker.1 H)))),
      fun H => MonoidHom.mem_ker.2 (Units.ext ((he h).1.symm.trans (by rw [H]; rfl)))⟩
  have hne : ∃ z, D.sp.cm.sig z ≠ z := by
    by_contra h
    push Not at h
    have hs : Function.Surjective (algebraMap D.host.F D.host.E) := fun z => (D.sp.cm.fixed z).1 (h z)
    have h1 : Module.finrank D.host.F D.host.E = 1 :=
      Algebra.finrank_eq_one_iff_bijective_algebraMap.2 ⟨(algebraMap D.host.F D.host.E).injective, hs⟩
    have h2 := D.sp.cm.deg2
    omega
  have hd := GlobalTheory.RealApprox.dense_inf D.host.F D.host.E D.sp.cm.sig (fun x => star_star x) hne V.gram
    (GlobalTheory.AutFunCounterexample.gram_herm V) (GlobalTheory.AutFunCounterexample.gram_det_ne V)
  let Φ : HA (Ainf D.host.F) D.sp.cm.sig V.gram → GinfC V := fun x =>
    ⟨e.symm (x, 1), (hfin _).2 (by rw [e.apply_symm_apply])⟩
  have hΦc : Continuous Φ :=
    Continuous.subtype_mk (e.symm.continuous.comp (continuous_id.prodMk continuous_const)) _
  have hΦs : Function.Surjective Φ := by
    intro g
    refine ⟨(e g.1).1, Subtype.ext ?_⟩
    change e.symm ((e g.1).1, 1) = g.1
    rw [← (hfin g.1).1 g.2]
    exact e.symm_apply_apply g.1
  refine Dense.mono ?_ (hΦs.denseRange.dense_image hΦc hd)
  rintro _ ⟨x, ⟨γ₀, hγ₀, hx⟩, rfl⟩ τ a b
  have hm := (he (e.symm (x, 1))).2
  rw [e.apply_symm_apply] at hm
  have key : compAt θ τ (Formalism.L2.Theta.mt V (Φ x).1) a b = tauE D τ (γ₀.1 a b) := by
    change infMat D.sp.cm.sig V.gram (θ τ) (e.symm (x, 1)) a b = _
    unfold infMat
    rw [← hm, ← hx]
    exact (hθ τ).1 _
  rw [key]
  have h0 : IsAlgebraic ℚ (γ₀.1 a b) := Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (γ₀.1 a b)
  first
    | exact h0.algHom (tauE D τ).toRatAlgHom
    | exact IsAlgebraic.map (tauE D τ).toRatAlgHom h0
    | exact (isAlgebraic_algHom_iff (tauE D τ).toRatAlgHom (tauE D τ).injective).2 h0

end GlobalTheory.RealAlgDense
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_unitaryRealPoints_algebraicEntries : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ V : HSp D, Dense {g : GinfC V | ∀ τ a b, IsAlgebraic ℚ (compAt θ τ (Formalism.L2.Theta.mt V g.1) a b)} := by
  atlas_forward_decl GlobalTheory.RealAlgDense.dense_alg
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBottom_weilAction_fockPureTensor_substitution : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ (t : T) (g : GA D A) (P : MvPolynomial (FVar D WW.rank A.rank) ℂ), (X.ω t).toSgn true ((GlobalTheory.Grid.ofSgn true A).symm g, 1) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) = pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B ((X.ω t).toSgn true ((GlobalTheory.Grid.ofSgn true A).symm g, 1) (X.f t)) (GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt A g)) P) := by
  first | exact @GlobalTheory.BottomAct.om_pureTensorO_bottom | exact GlobalTheory.BottomAct.om_pureTensorO_bottom | (intros; apply GlobalTheory.BottomAct.om_pureTensorO_bottom <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.RealAvg

open MvPolynomial

variable {D : D7}

theorem substMat_mul (θ : InfFam D) (V : HSp D) (m : ℕ) (d : D.what₂.Tau →₀ ℕ) (g₁ g₂ : GA D V) :
    substMat θ V m d (g₁ * g₂) = substMat θ V m d g₁ * substMat θ V m d g₂ := by
  ext k' k
  simp only [substMat, Matrix.mul_apply]
  have e : (fun τ => compAt θ τ (Formalism.L2.Theta.mt V (g₁ * g₂))) =
      (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g₁)) * (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g₂)) :=
    funext fun τ => GlobalTheory.StdUnn.CartanMove.compAt_mt_mul θ τ V g₁ g₂
  have e1 : (fun _ : D.what₂.Tau => (1 : Matrix (Fin m) (Fin m) ℂ)) = (fun _ => 1) * (fun _ => 1) := by
    funext τ; simp
  have e2 : GlobalTheory.CompactHowe.substF (fun _ : D.what₂.Tau => (1 : Matrix (Fin m) (Fin m) ℂ))
      (fun τ => compAt θ τ (Formalism.L2.Theta.mt V (g₁ * g₂))) (monomial k.1 1) =
      GlobalTheory.CompactHowe.substF (fun _ : D.what₂.Tau => (1 : Matrix (Fin m) (Fin m) ℂ))
        (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g₁))
        (GlobalTheory.CompactHowe.substF (fun _ : D.what₂.Tau => (1 : Matrix (Fin m) (Fin m) ℂ))
          (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g₂)) (monomial k.1 1)) := by
    rw [GlobalTheory.T.matrixFamilyBilateralSubstitution_comp_eq_mul, ← e, ← e1]
  rw [e2]
  conv_lhs => rw [eq_sum_mon (d := d) (GlobalTheory.CompactHowe.substF _ _ (monomial k.1 1))
    (fun k'' h => (GlobalTheory.T.mapDomain_fst_eq_of_coeff_matrixFamilyBilateralSubstitution_ne_zero _ _ _ _ h).trans k.2)]
  rw [map_sum, coeff_sum]
  refine Finset.sum_congr rfl fun k'' _ => ?_
  rw [map_smul, coeff_smul, smul_eq_mul, mul_comm]

theorem substMat_cont {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (m : ℕ) (d : D.what₂.Tau →₀ ℕ)
    (k' k : Mon D m V.rank d) :
    Continuous (fun g : GinfC V => substMat θ V m d g.1 k' k) := by
  have hc := (GlobalTheory.T.coeff_matrixFamilyBilateralSubstitution_monomial_continuous_algebraic (ι := D.what₂.Tau) (N := m) (n := V.rank) k.1 k'.1).1
  have hm : Continuous fun g : GinfC V => (fun τ : D.what₂.Tau => compAt θ τ (Formalism.L2.Theta.mt V g.1)) :=
    continuous_pi fun τ =>
      (GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp ((GlobalTheory.RealWeil.continuous_mt V).1.comp continuous_subtype_val)
  have hp : Continuous fun g : GinfC V => ((fun _ : D.what₂.Tau => (1 : Matrix (Fin m) (Fin m) ℂ)),
      (fun τ : D.what₂.Tau => compAt θ τ (Formalism.L2.Theta.mt V g.1))) := continuous_const.prodMk hm
  have := hc.comp hp
  exact this

theorem substMat_alg (θ : InfFam D) (V : HSp D) (m : ℕ) (d : D.what₂.Tau →₀ ℕ)
    (k' k : Mon D m V.rank d) (g : GA D V) (hg : ∀ τ a b, IsAlgebraic ℚ (compAt θ τ (Formalism.L2.Theta.mt V g) a b)) :
    IsAlgebraic ℚ (substMat θ V m d g k' k) := by
  have ha := (GlobalTheory.T.coeff_matrixFamilyBilateralSubstitution_monomial_continuous_algebraic (ι := D.what₂.Tau) (N := m) (n := V.rank) k.1 k'.1).2
    (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g)) (one_alg m) hg
  exact ha

theorem substMat_central (θ : InfFam D) (V : HSp D) (m : ℕ) (d : D.what₂.Tau →₀ ℕ) (z : GA D V) (τ₀ : D.what₂.Tau) (ζ : ℂ)
    (h1 : compAt θ τ₀ (Formalism.L2.Theta.mt V z) = ζ • (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (h2 : ∀ ρ, ρ ≠ τ₀ → compAt θ ρ (Formalism.L2.Theta.mt V z) = 1) :
    substMat θ V m d z = (ζ ^ d τ₀) • (1 : Matrix (Mon D m V.rank d) (Mon D m V.rank d) ℂ) := by
  classical
  have e : (fun ρ => compAt θ ρ (Formalism.L2.Theta.mt V z)) =
      fun ρ => if ρ = τ₀ then ζ • (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) else 1 := by
    funext ρ
    by_cases hρ : ρ = τ₀
    · subst hρ; rw [if_pos rfl, h1]
    · rw [if_neg hρ, h2 ρ hρ]
  ext k' k
  simp only [substMat, e, GlobalTheory.T.matrixFamilyBilateralSubstitution_scalar_monomial, coeff_smul, coeff_monomial, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  rw [show Finsupp.mapDomain Prod.fst k.1 = d from k.2]
  by_cases h : k' = k
  · subst h; simp
  · have h' : (k.1 : FVar D m V.rank →₀ ℕ) ≠ k'.1 := fun e => h (Subtype.ext e.symm)
    simp [h, h']

end GlobalTheory.RealAvg

namespace GlobalTheory.RealAvg

open MvPolynomial
open GlobalTheory.Grid (neg sgn ofSgn)

theorem avg_kernel_alg : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ dg : D.what₂.Tau →₀ ℕ, ∀ (κ : Measure (GinfC A)), κ.IsMulLeftInvariant → IsProbabilityMeasure κ →
      ∀ (t : T), ∀ x ∈ GfC A, ∀ h ∈ GfC WW, ∀ k : FVar D WW.rank A.rank →₀ ℕ,
        ∃ (m : ℕ) (r : Fin m → ℂ) (kk : Fin m → (FVar D WW.rank A.rank →₀ ℕ)), (∀ p, IsAlgebraic ℚ (r p)) ∧
          (∀ p, Finsupp.mapDomain Prod.fst (kk p) = dg) ∧
          ∫ g, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h (x * (g : GA D A)) ∂κ =
            ∑ p, r p * X.ker W.ψ W.θ t (MvPolynomial.monomial (kk p) 1) h x := by
  intro D T _ L μ₀ sc G W i j A A' WW X hPr hN hL hX
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  have hgA : A.gram = 1 := hX.std.1
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig A.gram
  haveI : BorelSpace (GA D A) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig A.gram
  haveI : CompactSpace (GinfC A) := isCompact_iff_compactSpace.1 (GlobalTheory.T.isCompact_unitaryRealPoints_of_gram_eq_one D A hgA)
  haveI : BorelSpace (GinfC A) := Subtype.borelSpace _
  obtain ⟨χ, hχc, hχ, hχa⟩ := GlobalTheory.T.exists_archimedean_character_theta hPr hN hL hX
  have hΓ := GlobalTheory.T.dense_unitaryRealPoints_algebraicEntries D W.θ hθ A

  let ρ : ∀ d : D.what₂.Tau →₀ ℕ, GinfC A →* Matrix (Mon D WW.rank A.rank d) (Mon D WW.rank A.rank d) ℂ := fun d =>
    { toFun := fun g => χ g • substMat W.θ A WW.rank d g.1
      map_one' := by simp only [map_one, OneMemClass.coe_one, substMat_one, one_smul]
      map_mul' := fun a b => by
        simp only [map_mul, Subgroup.coe_mul, substMat_mul]
        rw [smul_mul_smul_comm] }
  have hρ : ∀ d g, ρ d g = χ g • substMat W.θ A WW.rank d g.1 := fun _ _ => rfl
  have hρc : ∀ d, Continuous (ρ d) := fun d => by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [hρ, Matrix.smul_apply, smul_eq_mul]
    exact hχc.mul (substMat_cont hθ A WW.rank d a b)
  have hρa : ∀ d, ∀ γ ∈ {g : GinfC A | ∀ τ a b, IsAlgebraic ℚ (compAt W.θ τ (Formalism.L2.Theta.mt A g.1) a b)}, ∀ a b,
      IsAlgebraic ℚ (ρ d γ a b) := fun d γ hγ a b => by
    simp only [hρ, Matrix.smul_apply, smul_eq_mul]
    exact (hχa γ hγ).mul (substMat_alg W.θ A WW.rank d a b γ.1 hγ)

  have hker : ∀ t P h (g : GA D A), X.ker W.ψ W.θ t P h g = thetaKO ((X.ω t).toSgn true) ((ofSgn true A).symm g) h
      (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) := fun t P h g => by
    show thetaKO (X.ω t) g h _ = (X.ω t) ((ofSgn true A) ((ofSgn true A).symm g), h) _ 0
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hform : ∀ d t (x : GA D A) h (g : GinfC A) (k : Mon D WW.rank A.rank d),
      X.ker W.ψ W.θ t (monomial k.1 1) h (x * g.1) =
        ∑ k'' : Mon D WW.rank A.rank d, ρ d g k'' k * X.ker W.ψ W.θ t (monomial k''.1 1) h x := by
    intro d t x h g k
    rw [hker, map_mul]
    unfold thetaKO
    have e : ((ofSgn true A).symm x * (ofSgn true A).symm g.1, h) =
        ((ofSgn true A).symm x, h) * ((ofSgn true A).symm g.1, (1 : GA D WW)) := by
      rw [Prod.mk_mul_mk, mul_one]
    rw [e, map_mul, Module.End.mul_apply, GlobalTheory.T.definiteBottom_weilAction_fockPureTensor_substitution hX t g.1, hχ t g, GlobalTheory.FiniteFock.pureTensorO_smul]
    conv_lhs => rw [eq_sum_mon (d := d) (GlobalTheory.CompactHowe.substF _ _ (monomial k.1 1))
      (fun k'' hk => (GlobalTheory.T.mapDomain_fst_eq_of_coeff_matrixFamilyBilateralSubstitution_ne_zero _ _ _ _ hk).trans k.2)]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hρ, Matrix.smul_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k'' _ => ?_
    rw [hker]
    unfold thetaKO substMat
    ring

  have he : ‖Complex.exp Complex.I‖ = 1 := by simpa using Complex.norm_exp_ofReal_mul_I 1
  choose z hz _hzc h1 h2 using fun τ => GlobalTheory.CentralUnit.exists_central_of_norm_one D W.θ hθ A τ (Complex.exp Complex.I) he
  let c : D.what₂.Tau → ℂ := fun τ => χ ⟨z τ, hz τ⟩
  have hcen : ∀ d τ, ρ d ⟨z τ, hz τ⟩ = (c τ * Complex.exp Complex.I ^ d τ) • 1 := fun d τ => by
    rw [hρ, substMat_central W.θ A WW.rank d (z τ) τ _ (h1 τ) (h2 τ), smul_smul]
  obtain ⟨dg, hdg⟩ : ∃ dg : D.what₂.Tau →₀ ℕ, ∀ d, d ≠ dg → ∃ τ, c τ * Complex.exp Complex.I ^ d τ ≠ 1 := by
    by_cases hex : ∃ d : D.what₂.Tau →₀ ℕ, ∀ τ, c τ * Complex.exp Complex.I ^ d τ = 1
    · obtain ⟨d₀, hd₀⟩ := hex
      refine ⟨d₀, fun d hd => ?_⟩
      by_contra hall
      push_neg at hall
      refine hd (Finsupp.ext fun τ => ?_)
      have hc0 : c τ ≠ 0 := fun h0 => by have := hd₀ τ; rw [h0, zero_mul] at this; exact zero_ne_one this
      exact GlobalTheory.ExpPow.pow_exp_I_or_inv_injective _ _ _ (Or.inl rfl)
        (mul_left_cancel₀ hc0 ((hall τ).trans (hd₀ τ).symm))
    · push_neg at hex
      exact ⟨0, fun d _ => hex d⟩
  refine ⟨dg, fun κ hκ hκp t x _ h _ k => ?_⟩
  haveI := hκp
  set d := Finsupp.mapDomain Prod.fst k with hd
  let kM : Mon D WW.rank A.rank d := ⟨k, hd.symm⟩
  have hexp := integral_expand κ (fun g => ρ d g) (hρc d) (fun k'' => X.ker W.ψ W.θ t (monomial k''.1 1) h x)
    (fun g : GinfC A => X.ker W.ψ W.θ t (monomial k 1) h (x * g.1)) kM (fun g => hform d t x h g kM)
  by_cases hdd : d = dg
  · let e := Fintype.equivFin (Mon D WW.rank A.rank d)
    refine ⟨Fintype.card (Mon D WW.rank A.rank d), fun p => ∫ g, ρ d g (e.symm p) kM ∂κ, fun p => (e.symm p).1,
      fun p => GlobalTheory.HaarAlg.isAlgebraic_integral κ (ρ d) (hρc d) _ hΓ (hρa d) _ _,
      fun p => (show Finsupp.mapDomain Prod.fst (e.symm p).1 = d from (e.symm p).2).trans hdd, ?_⟩
    rw [hexp, ← Equiv.sum_comp e.symm]
  · obtain ⟨τ, hτ⟩ := hdg d hdd
    refine ⟨0, Fin.elim0, Fin.elim0, fun p => p.elim0, fun p => p.elim0, ?_⟩
    rw [hexp, Fin.sum_univ_zero]
    refine Finset.sum_eq_zero fun k'' _ => ?_
    rw [integral_eq_zero_of_scalar κ (ρ d) (hρc d) ⟨z τ, hz τ⟩ _ hτ (hcen d τ), zero_mul]

end GlobalTheory.RealAvg
end
end
