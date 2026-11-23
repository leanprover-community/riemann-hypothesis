module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.AdjMulSelf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.GramCore
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.OfMap

@[expose] public section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Pp

theorem UpperTheory.V.Ws.Pp.spIwa :
    ∀ {F : Type} [Field F] (V : ValuationSubring F) (h : M4 F), IsGSp 1 h → ∃ k : M4 V, IsGSp 1 k ∧ IsUp (adj (k.map V.subtype) * h) := by
  intro F _ V h hh
  let f : V →+* F := V.subtype
  let hU : GL (Fin 4) F := ⟨h, adj h, mul_adj_self hh, adj_mul_self hh⟩
  obtain ⟨k0, b, hb, hk⟩ := GlobalTheory.ValIwasawa.iwasawa V F 4 hU
  have hbU : IsUp (b : M4 F) := (isUp_iff _).mpr hb
  have hbi : IsUp ((b⁻¹ : GL (Fin 4) F) : M4 F) := IsUp_inv hbU
  have hKmap : (k0 : M4 V).map f = h * ((b⁻¹ : GL (Fin 4) F) : M4 F) := by
    have h1 : (hU : M4 F) =
        ((Matrix.GeneralLinearGroup.map (algebraMap V F) k0 : GL (Fin 4) F) : M4 F) * (b : M4 F) := by
      rw [hk]
      rfl
    have h2 : (hU : M4 F) = h := rfl
    rw [h2] at h1
    rw [h1, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rfl
  have hadjh : adj (h * ((b⁻¹ : GL (Fin 4) F) : M4 F)) * h = adj ((b⁻¹ : GL (Fin 4) F) : M4 F) := by
    rw [(grp F).1, Matrix.mul_assoc, adj_mul_self hh, Matrix.mul_one]
  have hmapadj : ∀ X : M4 V, adj (X.map f) = (adj X).map f := fun X => (grp V).2.2.2.2.2.1 F f X
  have upMap : ∀ X : M4 V, IsUp (X.map f) → IsUp X := by
    intro X hX i j hij
    have hz := hX i j hij
    simpa [f] using hz
  have hQ : IsUp (adj (k0 : M4 V) * (k0 : M4 V)) := by
    apply upMap
    rw [Matrix.map_mul, ← hmapadj, hKmap, (grp F).1, Matrix.mul_assoc,
      ← Matrix.mul_assoc (adj h), adj_mul_self hh, Matrix.one_mul]
    exact IsUp_mul (IsUp_adj hbi) hbi
  obtain ⟨t, ht, hkt⟩ := gram k0 hQ
  refine ⟨(k0 : M4 V) * (t : M4 V), hkt, ?_⟩
  have htU : IsUp ((t : M4 V).map f) := by
    intro i j hij
    simp [ht i j hij]
  rw [Matrix.map_mul, (grp F).1, hKmap, Matrix.mul_assoc, hadjh]
  exact IsUp_mul (IsUp_adj htU) (IsUp_adj hbi)
