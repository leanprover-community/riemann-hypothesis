module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantZmodLift
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundTheorem
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.ellC_of :
    UpperTheory.Gal.Wt.EllC := by
  intro E _ _ _ a C hC hneat
  set D : Subgroup (UA E a) := C ⊔ infU E a with hDdef
  have hDC : D ≤ C.comap GlobalTheory.EllU.finPart := sup_le (fun c hc => by
      change GlobalTheory.EllU.finPart c ∈ C
      rw [GlobalTheory.EllU.finPart_of_finU (hC hc)]; exact hc)
    (fun x hx => by
      change GlobalTheory.EllU.finPart x ∈ C
      rw [GlobalTheory.EllU.finPart_of_infU hx]; exact C.one_mem)
  let f : D →* C := (GlobalTheory.EllU.finPart.comp D.subtype).codRestrict C (fun d => hDC d.2)
  have hyp : ∀ g : UA E a, ∀ γ ∈ ratU E a, ∀ d : D, γ * g = g * d → f d = 1 := by
    intro g γ hγ d h
    have hfd : GlobalTheory.EllU.finPart (d : UA E a) ∈ C := hDC d.2
    have e : γ * g = g * GlobalTheory.EllU.finPart (d : UA E a) * ((GlobalTheory.EllU.finPart (d : UA E a))⁻¹ * (d : UA E a)) := by
      rw [h]; group
    have h1 := hneat g γ hγ _ hfd _ (GlobalTheory.EllU.inv_finPart_mul_mem (d : UA E a)) e
    exact Subtype.ext h1
  obtain ⟨ℓ, h1, h2⟩ := UpperTheory.Gal.Gen.ellGrp_holds (UA E a) C (ratU E a) D f hyp
  have hinf : ∀ x ∈ infU E a, ∀ g, ℓ (g * x) = ℓ g := by
    intro x hx g
    have e : f ⟨x, le_sup_right (a := C) hx⟩ = 1 := Subtype.ext (GlobalTheory.EllU.finPart_of_infU hx)
    have := h2 g ⟨x, le_sup_right (a := C) hx⟩
    simp only [e, mul_one] at this
    exact this
  have hC' : ∀ (c : C) g, ℓ (g * c) = ℓ g * c := by
    intro c g
    have e : f ⟨c, le_sup_left (b := infU E a) c.2⟩ = c := Subtype.ext (GlobalTheory.EllU.finPart_of_finU (hC c.2))
    have := h2 g ⟨c, le_sup_left (b := infU E a) c.2⟩
    simp only [e] at this
    exact this
  exact ⟨ℓ, ⟨h1, hC', hinf⟩⟩
