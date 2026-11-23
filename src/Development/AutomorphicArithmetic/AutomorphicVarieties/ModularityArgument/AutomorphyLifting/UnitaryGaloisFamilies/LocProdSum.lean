module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProductStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AbsCentral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsIrreducibleIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.IrrCaseT

@[expose] public section

open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.UnitaryBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem locProd_sum {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {ε : EpsFamily A} (L : LawsV a ha ε rc) :
    ∀ {c n : ℕ} {N : Fin c → ℕ} (hn : ∑ i, N i = n) (σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E)))
      (τ : SmIrr (GL (Fin n) (w.adicCompletion E))), Nonempty (τ.ρ.Equiv (locProd hn w σ)) →
      rc (cl τ) = sumList (List.ofFn fun i => rc (cl (σ i))) := by
  intro c
  induction c with
  | zero =>
    intro n N hn σ τ e
    obtain rfl : n = 0 := by simpa using hn.symm
    obtain ⟨e⟩ := e
    obtain ⟨φ⟩ := SupportRing.nonempty_equiv_unit (k := w.adicCompletion E) (stdBlocks N hn) fun i => (σ i).ρ
    have h1 := L.det 0 1 isSmoothChar_one
    simp only [List.range_zero, List.map_nil] at h1
    rw [List.ofFn_zero]
    refine (congrArg rc (IrrGL.of_eq_of.2 ⟨e.trans φ⟩)).trans h1
  | succ s ih =>
    intro n N hn σ τ e
    obtain rfl : n = N 0 + ∑ i : Fin s, N i.succ := hn.symm.trans (Fin.sum_univ_succ N)
    obtain ⟨e⟩ := e
    obtain ⟨E₁⟩ := MultiIrr.nonempty_prod₂_equiv_multiProd_succ (k := w.adicCompletion E) N hn fun i => (σ i).ρ
    have hs : IsSmooth (multiProd (stdBlocks (fun i : Fin s => N i.succ) rfl) fun i : Fin s => (σ i.succ).ρ) :=
      isSmooth_parInd _ _
    have hi := GlobalTheory.T.isIrreducible_second_factor_of_irreducible_product _ _ _ _ _ _ (σ 0).ρ _ τ.ρ (σ 0).smooth (σ 0).irred hs τ.irred ⟨e.trans E₁.symm⟩
    let σ' : SmIrr (GL (Fin (∑ i : Fin s, N i.succ)) (w.adicCompletion E)) := ⟨_, _, hs, hi⟩
    have h1 := L.prod (N 0) _ (ParLaws.toRep (σ 0)) (ParLaws.toRep σ') (ParLaws.toRep τ) ⟨e.trans E₁.symm⟩
    have h2 := ih (N := fun i : Fin s => N i.succ) rfl (fun i => σ i.succ) σ' ⟨.refl _⟩
    rw [List.ofFn_succ]
    exact h1.trans (congrArg _ h2)
