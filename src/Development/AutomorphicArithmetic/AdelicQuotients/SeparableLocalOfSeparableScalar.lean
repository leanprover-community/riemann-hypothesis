module

public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

open NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
theorem UpperTheory.separableLocal_of_separableScalar :
    SepSc → CentLoc → SepLoc := by
  intro hS hC F _ _ n γ hγ
  have hsep : (γ : Matrix (Fin n) (Fin n) F).charpoly.Separable := hγ
  have hI : ((pI F n (AdelicGLn.diagonal F n γ)).val : Matrix (Fin n) (Fin n) (InfiniteAdeleRing F)) =
      (γ : Matrix (Fin n) (Fin n) F).map (algebraMap F (InfiniteAdeleRing F)) := by
    ext a b
    rfl
  have hIs : (pI F n (AdelicGLn.diagonal F n γ)).val.charpoly.Separable := by
    rw [hI, Matrix.charpoly_map]
    exact hsep.map
  refine ⟨hIs, fun s => ?_, fun v => ?_⟩
  · obtain ⟨⟨r, hr⟩, -⟩ := hC F n ⟨Real.exp s, Real.exp_pos s⟩
    have h := hr (pI F n (AdelicGLn.diagonal F n γ))
    have h' : (pI F n (zA F n s) * pI F n (AdelicGLn.diagonal F n γ)).val =
        (r : InfiniteAdeleRing F) • (pI F n (AdelicGLn.diagonal F n γ)).val := h
    rw [h']
    exact hS _ n r _ hIs
  · have hv : ((finAt v (AdelicGLn.diagonal F n γ)).val : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
        (γ : Matrix (Fin n) (Fin n) F).map (algebraMap F (v.adicCompletion F)) := by
      ext a b
      rfl
    rw [hv, Matrix.charpoly_map]
    exact hsep.map
