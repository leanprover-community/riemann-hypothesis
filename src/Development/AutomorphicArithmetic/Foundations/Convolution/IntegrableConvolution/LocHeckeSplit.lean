module

public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.MatchProd
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SphLaws
public import GroundTheory.GlobalFields.KummerTheory.Splitting
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt

@[expose] public section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo

namespace UpperTheory.ConvolutionTheory.L1

private theorem isSph_cvAll {K : Type} [Field K] [NumberField K] {n : ℕ} {v : Pl K}
    [MeasurableSpace (GL (Fin n) (v.adicCompletion K))] [BorelSpace (GL (Fin n) (v.adicCompletion K))]
    (mF : Measure (GL (Fin n) (v.adicCompletion K))) (hH : mF.IsHaarMeasure)
    (h1 : mF (GLnLocal.integralGL (v.adicCompletion K) n) = 1) :
    ∀ (m : ℕ) (p : Fin (m + 1) → MvPolynomial (Fin n) ℂ) (φ : Fin (m + 1) → GL (Fin n) (v.adicCompletion K) → ℂ),
      (∀ i, GM.IsSph v (p i) (φ i)) → GM.IsSph v (∏ i, p i) (cvAll mF m φ)
  | 0, p, φ, h => by simpa [cvAll] using h 0
  | m + 1, p, φ, h => by
    rw [Fin.prod_univ_succ]
    exact (sphLaws.2 K n v).2.2 mF hH h1 _ _ _ _ (h 0)
      (isSph_cvAll mF hH h1 m (Fin.tail p) (Fin.tail φ) fun i => h i.succ)

end UpperTheory.ConvolutionTheory.L1

open GroundTheory.Global.SemiLocal in
theorem UpperTheory.ConvolutionTheory.L1.locHeckeSplit :
    UpperTheory.ConvolutionTheory.GM.LocHeckeSplit := by
  intro F E _ _ _ _ _ _ σ hσ hp n hn v hv p h f hh hf
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank F E = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
  obtain ⟨w₀⟩ := nonempty_placesOver E v
  obtain ⟨w, -, hM⟩ := UpperTheory.ConvolutionTheory.L1.matchProd F E σ hσ m hm n v w₀ hv
  intro _ _ _ _ mE mF hE hF h1E h1F
  have hc : ∀ u : PlacesOver E v, Continuous (h u) ∧ HasCompactSupport (h u) :=
    fun u => (UpperTheory.ConvolutionTheory.L1.sphLaws.2 E n u.1).1 _ _ (hh u)
  have hm' := hM h hc mF hF h1F
  have hs := UpperTheory.ConvolutionTheory.L1.isSph_cvAll mF hF h1F m (fun i => p (w i))
    (fun i g => h (w i) (mapGL n (completionMap v (w i).1) g))
    (fun i => UpperTheory.ConvolutionTheory.L1.sphLaws.1 F E v (w i) (hv (w i)) n _ _ (hh (w i)))
  have hprod : (∏ i, p (w i)) = ∏ᶠ u, p u := by
    rw [finprod_eq_prod_of_fintype]
    exact Equiv.prod_comp w p
  rw [hprod] at hs
  have key := (UpperTheory.ConvolutionTheory.L1.sphLaws.2 F n v).2.1 _ _ _ hs hf
  rw [key] at hm'
  exact hm' mE mF hE hF h1E h1F
