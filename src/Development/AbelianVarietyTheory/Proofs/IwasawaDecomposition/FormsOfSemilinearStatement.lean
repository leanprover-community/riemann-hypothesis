module

public import Formalism.LocalToGlobal.Divisibility.RowLat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsOfSemilinear
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Module NumberField Formalism.L2.DIV Formalism.DivisionValues
open scoped Matrix

theorem _root_.GlobalTheory.T.forms_of_semilinear_alt : ∀ {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K'] {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 Pl0' : Type} (φ : K →+* K') (e : G ≃* G') (B : BlockDat K G Pl0) (B' : BlockDat K' G' Pl0') (Z : Submodule K B.S.Forms) (Z' : Submodule K' B'.S.Forms) (L : B.S.Forms →+ B'.S.Forms),
  (∀ (a : K) (f : B.S.Forms), L (a • f) = φ a • L f) →
  LinearIndependent K' (fun k => L (B.S.basis k)) → ⊤ ≤ Submodule.span K' (Set.range fun k => L (B.S.basis k)) →
  (∀ f g : B.S.Forms, B'.S.csum (L f : B'.S.Cl → B'.S.V) (L g) = φ (B.S.csum f g)) →
  (∀ (g : G) (f : B.S.Forms), B'.r (e g) (L f) = L (B.r g f)) →
  (∀ f' : B'.S.Forms, (∀ c, (f' : B'.S.Cl → B'.S.V) c ∈ B'.S.Nab c) ↔ f' ∈ Submodule.span (𝓞 K') (L '' {f : B.S.Forms | ∀ c, (f : B.S.Cl → B.S.V) c ∈ B.S.Nab c})) →
  Z' = Submodule.span K' (L '' (Z : Set B.S.Forms)) →
  ∃ C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K', Function.Bijective C.mulVec ∧
    Cᴴ * B'.S.H * C = B.S.H.map φ ∧
    (∀ g : G, B'.S.actMat B'.r (e g) * C = C * (B.S.actMat B.r g).map φ) ∧
    B'.S.nabLat = Submodule.span (𝓞 K') ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K))) ∧
    B'.coord Z' = Submodule.span K' ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.coord Z : Set (Fin B.S.dim → K))) := by
  first | exact @GlobalTheory.Mem.R3.DefLatBC.forms_of_semilinear | exact GlobalTheory.Mem.R3.DefLatBC.forms_of_semilinear | (intros; apply GlobalTheory.Mem.R3.DefLatBC.forms_of_semilinear <;> assumption)
