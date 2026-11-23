module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyValuesDetOmegaDeltaLocalUnits
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.thetaKeyValues_detOmega_delta_local_units : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → KeyLoc κ →
  ∀ (S : Scheme.{0}) [IsIntegral S] (s : S ⟶ Sp ℤ) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), 1 ≤ g → Geo.Tor.IsNormalScheme S → LocallyOfFiniteType s →
    CharZero Γ(S, ⊤) → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → (abLocus G).Nonempty → IsOpen (abLocus G) →
    L.IsSymmetric → δ.IsLB → PolOnAb G L.L → UnifAlong G L.L → NzFib σ →
    ∃ f : (VB.det (LieVB.omega G) g).ι → δ.ι → S.presheaf.stalk (genericPoint S),
      (∀ c i, ∀ x ∈ (VB.det (LieVB.omega G) g).U c ⊓ δ.U i, ∃ (V : S.Opens) (_ : V ≤ (VB.det (LieVB.omega G) g).U c ⊓ δ.U i)
        (_ : x ∈ V) (u : Γ(S, V)ˣ), ∀ h : genericPoint S ∈ V, S.presheaf.germ V (genericPoint S) h (u : Γ(S, V)) = f c i) ∧
      (∀ c c' i i' (h1 : genericPoint S ∈ (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')
        (h2 : genericPoint S ∈ δ.U i ⊓ δ.U i'),
        f c i * S.presheaf.germ _ (genericPoint S) h2 (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i')) ^ 8 =
          S.presheaf.germ _ (genericPoint S) h1
            ((VB.det (LieVB.omega G) g).g c c' : Γ(S, (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')) ^ 4 * f c' i') := by
  first | exact @GlobalTheory.KeyValsPf.keyVals | exact GlobalTheory.KeyValsPf.keyVals | (intros; apply GlobalTheory.KeyValsPf.keyVals <;> assumption)
