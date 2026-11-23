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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

private theorem twNorm_hom' {G G' : Type} [Group G] [Group G'] (f : G →* G') (θ : Monoid.End G)
    (θ' : Monoid.End G') (h : ∀ x, f (θ x) = θ' (f x)) (m : ℕ) (δ : G) :
    f (PositivityTheory.Rg.Tf.Loc.twNorm θ m δ) = PositivityTheory.Rg.Tf.Loc.twNorm θ' m (f δ) := by
  have hp : ∀ (i : ℕ) (x : G), f ((θ ^ i) x) = (θ' ^ i) (f x) := fun i => by
    induction i with
    | zero => intro x; rfl
    | succ i ih =>
      intro x
      rw [PositivityTheory.Rg.Tf.Loc.pow_succ_apply', PositivityTheory.Rg.Tf.Loc.pow_succ_apply', h, ih]
  induction m with
  | zero => simp
  | succ m ih => rw [PositivityTheory.Rg.Tf.Loc.twNorm_succ, PositivityTheory.Rg.Tf.Loc.twNorm_succ, map_mul, ih, hp]

theorem UpperTheory.twistedNorm_local_of_compat :
    Compat → LocNorm := by
  intro hC F E _ _ _ _ _ _ σ _ n _ δ γ hδ
  obtain ⟨h1, h2, h3, h4, -, -, h7, h8⟩ := hC F E σ n
  have hdiag : GroundTheory.Automorphic.AdelicGLn.diagonal E n (PositivityTheory.Rg.Tf.Loc.normGL σ δ) =
      mapGL n (GroundTheory.Global.AdeleBaseChange.adeleMap F E) (GroundTheory.Automorphic.AdelicGLn.diagonal F n γ) := by
    rw [hδ, h8]
  constructor
  · have key := twNorm_hom' ((pI E n).comp (GroundTheory.Automorphic.AdelicGLn.diagonal E n)) (PositivityTheory.Rg.Tf.Loc.sigmaGL σ)
      (mapGL n (galInf σ)) (fun x => by
        simp only [MonoidHom.comp_apply]
        rw [← h7, h1]
        rfl) (Module.finrank F E) δ
    simp only [MonoidHom.comp_apply] at key
    rw [← key]
    change pI E n (GroundTheory.Automorphic.AdelicGLn.diagonal E n (PositivityTheory.Rg.Tf.Loc.normGL σ δ)) = _
    rw [hdiag, h3]
  · intro v
    have key := twNorm_hom' ((pE E n v).comp (GroundTheory.Automorphic.AdelicGLn.diagonal E n)) (PositivityTheory.Rg.Tf.Loc.sigmaGL σ)
      (mapGL n (galFin σ v)) (fun x => by
        simp only [MonoidHom.comp_apply]
        rw [← h7, h2]
        rfl) (Module.finrank F E) δ
    simp only [MonoidHom.comp_apply] at key
    rw [← key]
    change pE E n v (GroundTheory.Automorphic.AdelicGLn.diagonal E n (PositivityTheory.Rg.Tf.Loc.normGL σ δ)) = _
    rw [hdiag, h4]
    rfl
