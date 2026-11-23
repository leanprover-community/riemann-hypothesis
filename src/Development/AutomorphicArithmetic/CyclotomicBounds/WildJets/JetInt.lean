module

public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.BvvInt
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section
open Formalism.L2.Ker MvPolynomial

private noncomputable abbrev zPol (σ : Type) : Subring (MvPolynomial σ ℂ) :=
  (MvPolynomial.map (Int.castRingHom ℂ)).range

private theorem zX_mem {σ : Type} (v : σ) : (X v : MvPolynomial σ ℂ) ∈ zPol σ := ⟨X v, map_X _ _⟩

private theorem zcoeff {σ : Type} {p : MvPolynomial σ ℂ} (hp : p ∈ zPol σ) (m : σ →₀ ℕ) :
    ∃ z : ℤ, p.coeff m = (z : ℂ) := by
  obtain ⟨q, rfl⟩ := RingHom.mem_range.mp hp
  exact ⟨q.coeff m, by simp [MvPolynomial.coeff_map]⟩

private theorem zdet_mem {σ : Type} {s : ℕ} (M : Matrix (Fin s) (Fin s) (MvPolynomial σ ℂ))
    (h : ∀ p q, M p q ∈ zPol σ) : M.det ∈ zPol σ := by
  choose M' hM' using fun p q => RingHom.mem_range.mp (h p q)
  refine RingHom.mem_range.mpr ⟨(Matrix.of M').det, ?_⟩
  rw [RingHom.map_det]
  congr 1
  refine Matrix.ext fun p q => ?_
  simpa using hM' p q

private theorem zaeval_mem {σ τ : Type} {p : MvPolynomial σ ℂ} (hp : p ∈ zPol σ) (g : σ → MvPolynomial τ ℂ)
    (hg : ∀ v, g v ∈ zPol τ) : aeval g p ∈ zPol τ := by
  obtain ⟨q, rfl⟩ := RingHom.mem_range.mp hp
  clear hp
  induction q using MvPolynomial.induction_on with
  | C z =>
    refine RingHom.mem_range.mpr ⟨C z, ?_⟩
    simp [MvPolynomial.algebraMap_eq]
  | add p q hp' hq' =>
    rw [map_add (f := _), map_add (f := _)]
    exact add_mem hp' hq'
  | mul_X p v hp' =>
    rw [map_mul, map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X]
    exact mul_mem hp' (hg v)

variable {ι : Type} [Fintype ι] {a b : ℕ}

private theorem zsubD_mem {P : Pol ℂ ι a} (hP : P ∈ zPol (ι × Fin a × Fin a)) :
    subD ℂ ι a b P ∈ zPol ((ι × Fin b × Fin b) ⊕ DVar ι a b) := by
  unfold subD
  refine zaeval_mem hP _ fun v => ?_
  split_ifs
  · exact sum_mem fun β _ => mul_mem (zX_mem _) (zX_mem _)
  · exact zero_mem _

private theorem jetLin_mono (J : (DVar ι a b →₀ ℕ) → ℂ) (m : (ι × Fin b × Fin b) ⊕ DVar ι a b →₀ ℕ) (c : ℂ) :
    jetLin J (monomial m c) =
      monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) (c * J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  have e : (monomial m c : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) =
      c • (basisMonomials _ ℂ) m := by
    rw [MvPolynomial.coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul]
  simp only [jetLin, Module.Basis.constr_basis, smul_monomial, smul_eq_mul]

open Classical in
private theorem jetLin_zmem (k : DVar ι a b →₀ ℕ)
    {p : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ} (hp : p ∈ zPol _) :
    jetLin (fun m => if m = k then (1 : ℂ) else 0) p ∈ zPol (ι × Fin b × Fin b) := by

  rw [p.as_sum, map_sum]
  refine sum_mem fun μ _ => ?_
  rw [jetLin_mono]
  obtain ⟨z, hz⟩ := zcoeff hp μ
  refine RingHom.mem_range.mpr ⟨monomial (μ.comapDomain Sum.inl Sum.inl_injective.injOn)
    (z * if μ.comapDomain Sum.inr Sum.inr_injective.injOn = k then 1 else 0), ?_⟩
  rw [MvPolynomial.map_monomial, hz]
  split_ifs <;> simp

open Classical in
private theorem jetLin_split (p : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) :
    ∃ S : Finset (DVar ι a b →₀ ℕ), ∀ J : (DVar ι a b →₀ ℕ) → ℂ,
      jetLin J p = ∑ k ∈ S, J k • jetLin (fun m => if m = k then (1 : ℂ) else 0) p := by
  have hsplit : ∀ J' : (DVar ι a b →₀ ℕ) → ℂ, jetLin J' p = ∑ μ ∈ p.support,
      monomial (μ.comapDomain Sum.inl Sum.inl_injective.injOn)
        (AddMonoidAlgebra.coeff p μ * J' (μ.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
    intro J'
    conv_lhs => rw [p.as_sum]

    rw [map_sum]
    simp only [jetLin_mono]
  refine ⟨p.support.image (fun μ => μ.comapDomain Sum.inr Sum.inr_injective.injOn), fun J => ?_⟩
  rw [hsplit J]
  simp only [hsplit, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [Finset.sum_eq_single (μ.comapDomain Sum.inr Sum.inr_injective.injOn)]
  · simp [smul_monomial, mul_comm]
  · intro k _ hk
    simp [Ne.symm hk]
  · intro h
    exact absurd (Finset.mem_image_of_mem _ hμ) h

end

theorem UpperTheory.WildA.jetInt :
    ∀ {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ),
      Formalism.L2.Ker.JetInVV ℂ lam lam' n → ∀ (j : VVIdx lam) (i : VVIdx lam'),
      ∃ c : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) →₀ ℤ, ∀ J : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → ℂ,
        (bVV ℂ lam').repr (Formalism.L2.Ker.jetOp lam lam' J n (bVV ℂ lam j)) i = c.sum fun m z => (z : ℂ) * J m := by
  intro ι _ a b lam lam' n hV j i
  classical
  obtain ⟨P, hP⟩ : ∃ P, P = bVVfun ℂ lam j := ⟨_, rfl⟩
  have hPmem : P ∈ VV ℂ lam := by
    rw [hP, ← bVV_coe]
    exact ((bVV ℂ lam) j).2
  have hPz : P ∈ zPol (ι × Fin a × Fin a) := by
    obtain ⟨Q, hQ⟩ := bVVfun_int ℂ lam j
    rw [hP]
    exact RingHom.mem_range.mpr ⟨Q, hQ.symm⟩
  have hdet : ∀ τ, Formalism.L2.Ker.frDet ℂ a τ ∈ zPol (ι × Fin a × Fin a) := fun τ =>
    zdet_mem _ (fun p q => zX_mem _)
  have hsh : P * ∏ τ, Formalism.L2.Ker.frDet ℂ a τ ^ n τ ∈ zPol (ι × Fin a × Fin a) :=
    mul_mem hPz (prod_mem fun τ _ => pow_mem (hdet τ) _)
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = Formalism.L2.Ker.subD ℂ ι a b (P * ∏ τ, Formalism.L2.Ker.frDet ℂ a τ ^ n τ) := ⟨_, rfl⟩
  have hQz : Q ∈ zPol _ := by
    rw [hQ]
    exact zsubD_mem hsh
  have hJQ : ∀ J, Formalism.L2.Ker.jetMap J n P = Formalism.L2.Ker.jetLin J Q := by
    intro J
    rw [hQ]
    rfl
  obtain ⟨S, hS⟩ := jetLin_split Q
  have hint : ∀ k, ∃ z : ℤ, (bVV ℂ lam').repr
      ⟨Formalism.L2.Ker.jetMap (fun m => if m = k then (1 : ℂ) else 0) n P, hV _ P hPmem⟩ i = z := by
    intro k
    apply UpperTheory.WildA.bvvInt
    intro m
    apply zcoeff
    show Formalism.L2.Ker.jetMap (fun m => if m = k then (1 : ℂ) else 0) n P ∈ _
    rw [hJQ]
    exact jetLin_zmem k hQz
  choose z hz using hint
  refine ⟨∑ k ∈ S, Finsupp.single k (z k), fun J => ?_⟩
  have hop : Formalism.L2.Ker.jetOp lam lam' J n (bVV ℂ lam j) = ⟨Formalism.L2.Ker.jetMap J n P, hV J P hPmem⟩ := by
    show Formalism.L2.Ker.retrVV ℂ lam' (Formalism.L2.Ker.jetMap J n ((bVV ℂ lam j : Pol ℂ ι a))) = _
    have hb : ((bVV ℂ lam j : Pol ℂ ι a)) = P := by rw [bVV_coe, hP]
    rw [hb]
    exact Submodule.projectionOnto_apply_left _ ⟨_, hV J P hPmem⟩
  have hsum : (⟨Formalism.L2.Ker.jetMap J n P, hV J P hPmem⟩ : VV ℂ lam') =
      ∑ k ∈ S, J k • (⟨Formalism.L2.Ker.jetMap (fun m => if m = k then (1 : ℂ) else 0) n P, hV _ P hPmem⟩ : VV ℂ lam') := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul, hJQ]
    exact hS J

  rw [hop, hsum, map_sum, Finsupp.finsetSum_apply]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, hz]
  let f : ((Formalism.L2.Ker.DVar ι a b →₀ ℕ) →₀ ℤ) →+ ℂ :=
    { toFun := fun c => c.sum fun m z => (z : ℂ) * J m
      map_zero' := by simp
      map_add' := by
        intro x y
        exact Finsupp.sum_add_index' (by simp) (by intros; push_cast; ring) }
  change ∑ x ∈ S, J x * (z x : ℂ) = f (∑ k ∈ S, Finsupp.single k (z k))
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [f, Finsupp.sum_single_index, mul_comm]
