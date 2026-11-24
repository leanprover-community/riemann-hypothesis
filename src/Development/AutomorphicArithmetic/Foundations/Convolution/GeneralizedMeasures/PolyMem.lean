module

public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import GroundTheory.LocalFields.LocalFourierHaar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

private theorem haar_one {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (U : Subgroup G) (hc : IsCompact (U : Set G)) (ho : IsOpen (U : Set G)) :
    ∃ m : Measure G, m.IsHaarMeasure ∧ m U = 1 := by
  let K₀ : TopologicalSpace.PositiveCompacts G := ⟨⟨U, hc⟩, by
    rw [TopologicalSpace.Compacts.carrier_eq_coe, TopologicalSpace.Compacts.coe_mk, ho.interior_eq]
    exact ⟨1, U.one_mem⟩⟩
  exact ⟨Measure.haarMeasure K₀, inferInstance, Measure.haarMeasure_self (K₀ := K₀)⟩

private theorem poly_mem {n : ℕ} (p : MvPolynomial (Fin n) ℂ) :
    polyEmb (n := n) (aeval (fun i : Fin n => esymm (Fin n) ℂ (i + 1)) p) ∈
      symmetricLaurent (n := n) := fun σ => by
  rw [← polyEmb_rename]
  congr 1
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 2
  funext i
  exact MvPolynomial.esymm_isSymmetric (Fin n) ℂ _ σ

theorem UpperTheory.ConvolutionTheory.GM.sphEx :
    SphEx := by
  intro K _ _ n _ w
  refine ⟨fun p => ?_, ?_, ?_⟩
  · borelize (GL (Fin n) (w.adicCompletion K))
    obtain ⟨m, hm, h1⟩ := haar_one (GLnLocal.integralGL (w.adicCompletion K) n) (GLnLocal.isCompact_integralGL _ n)
      (GLnLocal.isOpen_integralGL _ n)
    obtain ⟨H, hH⟩ := (AlgHom.mem_range _).1 (symmetricLaurent_le_range (μ := m) (F := w.adicCompletion K) (poly_mem p))
    exact ⟨fun x => (H : HeckeAlgebra m) x, _, inferInstance, m, hm, h1, H, fun _ => rfl, hH⟩
  · borelize (GL (Fin n) (w.adicCompletion K))
    obtain ⟨m, hm, h1⟩ := haar_one (GLnLocal.integralGL (w.adicCompletion K) n) (GLnLocal.isCompact_integralGL _ n)
      (GLnLocal.isOpen_integralGL _ n)
    refine ⟨_, inferInstance, m, hm, h1, 1, fun x => ?_, by rw [map_one, map_one, map_one]⟩
    rw [HeckeAlgebra.HeckeAlgebraLevel.val_one]
    have hr : m.real (GLnLocal.integralGL (w.adicCompletion K) n : Set (GL (Fin n) (w.adicCompletion K))) = 1 := by
      simp [Measure.real, h1]
    rw [HeckeAlgebra.idem_apply, hr]
    simp only [Complex.ofReal_one, inv_one]
    rfl
  · rintro p h ⟨_, _, m, _, -, H, hH, -⟩
    obtain rfl : (fun x => (H : HeckeAlgebra m) x) = h := funext hH
    exact ⟨(H : HeckeAlgebra m).mem.1, (H : HeckeAlgebra m).mem.2,
      fun k hk x => HeckeAlgebra.HeckeAlgebraLevel.val_mem _ _ H k hk x⟩
