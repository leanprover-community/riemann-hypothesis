module

public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

open NumberField IsDedekindDomain

def GlobalDatumCompatibility (D : D7) : Prop :=
  Formalism.MainNotions.SphericalInertData.HypEFK D ∧
    (2 ≤ Module.finrank ℚ D.host.F ∧
      ∀ w : PlE D.host, ¬ IsSplitPl D.host w → ((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) ∧
    ∀ j, 1 ≤ j → j ≤ D.R.m → (letI := D.host.cmStar; (D.sp.V j).IsDefinite)

theorem nV_pos (D : D7) : 1 ≤ D.R.nV := by
  have := D.R.t_odd.pos
  show 1 ≤ D.R.r + D.R.t
  omega

theorem hypCM_of (D : D7) (hc : GlobalDatumCompatibility D) : Formalism.MainNotions.SphericalInertData.HypCM D := by
  refine ⟨?_, hc.2.1⟩
  letI := D.host.cmStar
  exact D.sp.cm.cmUnram

theorem base_change_automorphic_of (D : D7) (h45 : Formalism.MainNotions.SphericalInertData.Conclusion1 D) (hc : GlobalDatumCompatibility D) :
    Formalism.MainNotions.SumRepresentations.adm1 D := by
  intro i P
  obtain ⟨Pa, h1, h2, h3, h4, h5, h6⟩ :=
    h45 hc.1 (hypCM_of D hc) (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (nV_pos D)
      (hc.2.2 _ (D.nd.j_range i).1 (D.nd.j_range i).2) (D.nbc.embAV i P)
      (fun w hw => D.nbc.embAV_sph i P w hw)
  refine ⟨Pa, h1, h2, h3, fun w hw => (h4 w hw).trans (D.nbc.embAV_loc i P w).symm,
    fun w hw => ⟨(h5 w hw).1, (h5 w hw).2.trans (congrArg _ (D.nbc.embAV_sat i P w).symm)⟩,
    fun τ => (h6 τ).trans (congrFun (D.nbc.embAV_inf i P) τ).symm⟩

def LitBNIrr (Γ : Type) [Group Γ] : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (a : ℕ) (ρ ρ' : Γ →* GL (Fin a) (Formalism.CyclotomicNorms.Fbar ℓ)),
    (∀ g, ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Formalism.CyclotomicNorms.Fbar ℓ)).charpoly =
      ((ρ' g : GL _ _) : Matrix (Fin a) (Fin a) (Formalism.CyclotomicNorms.Fbar ℓ)).charpoly) →
    Formalism.CyclotomicNorms.IrredOn ρ' ⊤ → Formalism.CyclotomicNorms.IrredOn ρ ⊤

theorem charpoly_mapRep {Γ : Type} [Group Γ] {A B : Type} [CommRing A] [CommRing B] {a : ℕ}
    (f : A →+* B) (ρ : Γ →* GL (Fin a) A) (g : Γ) :
    ((mapRep f ρ g : GL _ _) : Matrix (Fin a) (Fin a) B).charpoly =
      (((ρ g : GL _ _) : Matrix (Fin a) (Fin a) A).charpoly).map f :=
  Matrix.charpoly_map _ f

end Formalism.MainNotions.N
