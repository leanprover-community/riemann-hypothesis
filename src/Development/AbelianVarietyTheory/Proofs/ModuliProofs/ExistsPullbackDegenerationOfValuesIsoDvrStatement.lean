module

public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ThetaTowerRecognition
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsFib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPullbackDegenerationOfValuesIsoDvr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.exists_pullbackDegeneration_of_values_iso_dvr : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D D' : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (J : NumD.Iso N N') (Ψ : D.P.A ≅ D'.P.A), IsMonHom Ψ.hom → LBIso D.P.L (D'.P.L.pull Ψ.hom.left) → ∀ (φ : TF (R := V) F ⊗ D.P.A ≅ TF (R := V) F ⊗ D'.P.A) (w : AbPartIso.BunIso φ), φ.hom ≫ fst _ _ = fst _ _ → φ.hom ≫ snd _ _ = snd _ _ ≫ Ψ.hom → w.IsGen → (∀ x, AbPartIso.Carries ν ν' φ x (J.φ x)) → (∀ x, (J.h x : F) * AbPartIso.wVal ν ν' w J.φ 1 = AbPartIso.wVal ν ν' w J.φ x) → ∃ e : IsPullDeg (RingHom.id V) D D', ∀ (k : ℕ) (p : QkPt D F k) (p' : QkPt D' F k) (q : N.QT k) (q' : N'.QT k), ν.QPt p q → ν'.QPt p' q' → q'.1.1.toAdd = J.e q.1.1.toAdd → J.Rel q.1.2 q'.1.2 → GlobalTheory.IndefiniteRowSideFullHecke.ThetaTowerRecognition.Carries e p p' := by
  first | exact @GlobalTheory.ValuesIdent.exists_isPullDeg_of_values | exact GlobalTheory.ValuesIdent.exists_isPullDeg_of_values | (intros; apply GlobalTheory.ValuesIdent.exists_isPullDeg_of_values <;> assumption)
