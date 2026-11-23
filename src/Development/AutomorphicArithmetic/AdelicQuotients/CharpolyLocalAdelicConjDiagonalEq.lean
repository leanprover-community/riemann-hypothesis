module

public import GroundTheory.AutomorphicForms.ReductionHeight
public import GroundTheory.AutomorphicForms.ReductionIwasawa
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
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.HeightLe
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.IsNormAlong
import GroundTheory.GlobalFields.Adele.BaseChange.FiniteMap
import GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap

@[expose] public section

open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

theorem UpperTheory.charpoly_local_adelic_conj_diagonal_eq :
    ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (γ : GL (Fin n) E) (x : AdelicGLn.AdelicGL E n),
        (∀ w : HeightOneSpectrum (𝓞 E), ((finAt w (x⁻¹ * AdelicGLn.diagonal E n γ * x) : GL (Fin n) (w.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (w.adicCompletion E)).charpoly = (γ : Matrix (Fin n) (Fin n) E).charpoly.map (algebraMap E (w.adicCompletion E))) ∧
        ∀ w : InfinitePlace E, ((infAt w (x⁻¹ * AdelicGLn.diagonal E n γ * x) : GL (Fin n) w.Completion) :
          Matrix (Fin n) (Fin n) w.Completion).charpoly = (γ : Matrix (Fin n) (Fin n) E).charpoly.map (algebraMap E w.Completion) := by
  intro E _ _ n γ x
  refine ⟨fun w => ?_, fun w => ?_⟩
  · have h : ((finAt w (AdelicGLn.diagonal E n γ) : GL (Fin n) (w.adicCompletion E)) :
        Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
        (γ : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E)) := by
      ext a b
      rfl
    rw [finAt_mul, finAt_mul, finAt_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
      Matrix.charpoly_units_conj', h, Matrix.charpoly_map]
  · have h : ((infAt w (AdelicGLn.diagonal E n γ) : GL (Fin n) w.Completion) :
        Matrix (Fin n) (Fin n) w.Completion) =
        (γ : Matrix (Fin n) (Fin n) E).map (algebraMap E w.Completion) := by
      ext a b
      rfl
    rw [infAt_mul, infAt_mul, infAt_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
      Matrix.charpoly_units_conj', h, Matrix.charpoly_map]
