module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ThetaSetupAlgebraMaps
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GalOCOkToOC
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

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

def limMod {R : Type} [CommRing R] {Γ : Type} (S : ℕ → Sys.{1} R) {σ : Γ → R →+* R} (act : ∀ j g, Sys.Hom (S j) (S j) (σ g)) :
    GMod R Γ where
  N j := (S j).lim
  act j g := (act j g).lim.toAddMonoidHom

def limAlg {R : Type} [CommRing R] {Γ : Type} (S : ℕ → Sys.{1} R) {σ : Γ → R →+* R} (act : ∀ j g, Sys.Hom (S j) (S j) (σ g))
    (one : ∀ n, (S 0).M n) (cup : ∀ n i j, (S i).M n → (S j).M n → (S (i + j)).M n) : GAlg R Γ where
  toGMod := limMod S act
  one x := ∀ n, (show (S 0).lim from x).1 n = one n
  cup {i j} x y z := ∀ n, (show (S (i + j)).lim from z).1 n = cup n i j ((show (S i).lim from x).1 n) ((show (S j).lim from y).1 n)

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

namespace Model

abbrev MS (M : Model l K) (j : ℕ) : Sys.{1} (Acris l) := MSys M.P j

def galS (M : Model l K) (j : ℕ) (σ : Gal(PadicAlgCl l/K)) : Sys.Hom (M.MS j) (M.MS j) (ACris.galCris σ) where
  f n := M.galMH σ n j
  comm n x := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => (PAlg.pdOk_twId σ _).red_acr n.le_succ _))

def phiS (M : Model l K) (j : ℕ) : Sys.Hom (M.MS j) (M.MS j) (ACris.phi (K := ℂ_[l]) (p := l)) where
  f n := M.phiMH n j
  comm n x := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => (PAlg.pdOk_frob _).red_acr n.le_succ _))

def pullS {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (j : ℕ) : Sys.Hom (N.MS j) (M.MS j) (RingHom.id _) where
  f n := pullMH u hu n j
  comm n x := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

def MA (M : Model l K) : GAlg (Acris l) K.fixingSubgroup :=
  limAlg M.MS (σ := fun g => ACris.galCris (IntermediateField.fixingSubgroupEquiv K g))
    (fun j g => M.galS j (IntermediateField.fixingSubgroupEquiv K g)) (fun n => CH.oneH (AcrEl M.P n))
    (fun n _ _ x y => (CH.mulP (AcrEl M.P n)).cup rfl x y)

end Model

end CrystallineSemistableComparison
