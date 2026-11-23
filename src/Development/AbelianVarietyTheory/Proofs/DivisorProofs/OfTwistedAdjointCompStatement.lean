module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfTwistedAdjointComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam


theorem _root_.GlobalTheory.T.of_twisted_adjoint_comp : ∀ (R : Type) [CommRing R] [IsDomain R] (Q₁ Q₂ : Data R) (a : Q₁.B ⟶ Q₂.B) (a₁ a₁' : Q₁.B ⟶ Q₁.B) (a' : Q₂.B ⟶ Q₁.B) (h : Q₁.X →+ Q₂.X) (h₁ h₁' : Q₁.X →+ Q₁.X) (h' : Q₂.X →+ Q₁.X), IsMonHom a → IsMonHom a' → (∀ y, Q₂.c (h y) = Q₁.c y ≫ a) → (∀ z, Q₁.c (h' z) = Q₂.c z ≫ a') → Adj Q₁ Q₁ a₁ a₁' h₁ h₁' → (∃ w : LB.Iso (cubeLB Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] Q₂.M.L) (cubeLB Q₁.B ![fst Q₁.B Q₂.B ≫ a₁, snd Q₁.B Q₂.B ≫ a'] Q₁.M.L), w.IsGen ∧ ∀ y y' z J₁ J₂, Good Q₁.M.L z J₁ → Good Q₂.M.L z J₂ → val (Q₂.tau (h y) y') (𝟙 _) z J₂ = adjVal w (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₂.c y')).left z J₁ J₂ * val (Q₁.tau (h₁ y) (h' y')) (𝟙 _) z J₁) → Adj Q₁ Q₂ a (a' ≫ a₁') h (h₁'.comp h') := by
  first | exact @GlobalTheory.MumFam.Adj.of_twisted_comp | exact GlobalTheory.MumFam.Adj.of_twisted_comp | (intros; apply GlobalTheory.MumFam.Adj.of_twisted_comp <;> assumption)
