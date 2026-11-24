module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsScale
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.AdelicLattice

theorem adelicLattice_selfDual : ∀ (I : AutInst) (y : Fin I.n → (I.E ⊗[I.F] Af I.F)), y ∈ I.Lf ↔ ∀ y' ∈ I.Lf, hAf I y' y ∈ IntAf I.F I.E := by
  intro I y
  have hsig : ((I.cm.sig : I.E →ₐ[I.F] I.E) : I.E →+* I.E) = starRingEnd I.E := by
    ext a
    rfl
  have hdual : ∀ x : Fin I.n → I.E, x ∈ I.L ↔ ∀ z ∈ I.L,
      Formalism.UG.hform ((I.cm.sig : I.E →ₐ[I.F] I.E) : I.E →+* I.E) I.J z x ∈
        (algebraMap (𝓞 I.E) I.E).range := by
    rw [hsig]
    exact I.L_dual

  have hgen : Set.range (fun x : I.L => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((x : Fin I.n → I.E) i)) =
      (fun x : Fin I.n → I.E => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)) '' (I.L : Set (Fin I.n → I.E)) := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hLf : ∀ u, u ∈ I.Lf ↔ u ∈ Submodule.span (IntAf I.F I.E)
      ((fun x : Fin I.n → I.E => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)) '' (I.L : Set (Fin I.n → I.E))) := by
    intro u
    show u ∈ Submodule.span _ _ ↔ _
    rw [hgen]
  constructor
  · intro hy y' hy'
    have hy'' := (hLf y').1 hy'
    unfold hAf
    induction hy using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨x, rfl⟩ := hv
      exact Formalism.UG.P.csDual_span I.cm.sig I.J I.L (x : Fin I.n → I.E) ((hdual _).1 x.2) y' hy''
    | zero =>
      rw [Formalism.UG.P.csScale_hform_zero_right]
      exact zero_mem _
    | add u v _ _ hu hv =>
      rw [Formalism.UG.P.csScale_hform_add_right]
      exact add_mem hu hv
    | smul c v _ hv =>
      rw [Subring.smul_def, Formalism.UG.P.csScale_hform_smul_right]
      exact mul_mem c.2 hv
  · intro h
    have hmem := GlobalTheory.PointLattice.mem_latS_of_integral (F := I.F) I.cm.sig I.J I.L hdual I.L_span y
      (fun w hw => h w ((hLf w).2 hw))
    exact (hLf y).2 hmem

end GlobalTheory.AdelicLattice
