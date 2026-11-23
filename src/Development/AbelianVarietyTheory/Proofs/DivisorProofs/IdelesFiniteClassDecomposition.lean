module

public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SatakeComb

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG

noncomputable section
namespace GlobalTheory.ClassCover

variable {L : Type} [Field L] [NumberField L]

def toIdeles : (FiniteAdeleRing (𝓞 L) L)ˣ →* Neutral.B1.Ideles L :=
  Units.map (MonoidHom.inr (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

theorem eq_diag_mul_of_classOf (y : (FiniteAdeleRing (𝓞 L) L)ˣ)
    (hc : ReciprocityTheory.Neutral.Bridge.HCFR.classOf L (toIdeles y) = 1) :
    ∃ (k : Lˣ) (u : (FiniteAdeleRing (𝓞 L) L)ˣ),
      (∀ P : HeightOneSpectrum (𝓞 L), Valued.v ((u : FiniteAdeleRing (𝓞 L) L) P) = 1) ∧
      y = Units.map (algebraMap L (FiniteAdeleRing (𝓞 L) L)).toMonoidHom k * u := by
  obtain ⟨k, u, hu, he⟩ := (ReciprocityTheory.Neutral.Bridge.HCFR.classOf_eq_one_iff L _).1 hc
  refine ⟨k, ⟨(u : AdeleRing (𝓞 L) L).2, ((u⁻¹ : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L).2, ?_, ?_⟩,
    fun P => (hu.2 P).1, ?_⟩
  · exact congrArg Prod.snd u.mul_inv
  · exact congrArg Prod.snd u.inv_mul
  · apply Units.ext
    have h2 : ((toIdeles y : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L).2 =
        ((Neutral.B1.diagUnits L k * u : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L).2 := by rw [he]
    exact h2

end GlobalTheory.ClassCover
