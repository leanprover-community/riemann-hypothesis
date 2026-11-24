module

public import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
public import Formalism.SharpRestriction.ParConsts
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

namespace Formalism.MainNotions.TwistedPlaces

open Formalism.BasicNotions Formalism.MainNotions

def FamilyThinScalesBound {eps : ℝ} (Fm : FamP eps) (C : ℝ) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, aux₃ (Fm.L x i) C

def OrbitValuationBound {eps : ℝ} (Fm : FamP eps) : Prop := ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, aux₃ (Fm.L x i) C

def AdmFC {eps : ℝ} (Fm : FamP eps) (C : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), admitted (Fm.L x i) (Fm.params x hx i) C

def AdmF {eps : ℝ} (Fm : FamP eps) : Prop := ∃ C : ℝ, AdmFC Fm C

def KudlaFamilyStatement {eps : ℝ} (Fm : FamP eps) : Prop := AdmF Fm → OrbitValuationBound Fm

def UniformExportStatement (eps : ℝ) : Prop := ∀ Ca : ℝ, ∃ C : ℝ, ∀ Fm : FamP eps, AdmFC Fm Ca → FamilyThinScalesBound Fm C

theorem stmtF_of_stmtU {eps : ℝ} (h : UniformExportStatement eps) (Fm : FamP eps) : KudlaFamilyStatement Fm := by
  rintro ⟨Ca, hA⟩
  obtain ⟨C, hC⟩ := h Ca
  obtain ⟨x0, h0⟩ := hC Fm hA
  exact ⟨C, x0, h0⟩

end Formalism.MainNotions.TwistedPlaces

namespace Formalism.MainNotions.ExportFamilies

open Formalism.BasicNotions Formalism.MainNotions

abbrev FamilyThinScalesBound {eps : ℝ} (Fm : FamP eps) (C : ℝ) : Prop := TwistedPlaces.FamilyThinScalesBound Fm C

abbrev OrbitValuationBound {eps : ℝ} (Fm : FamP eps) : Prop := TwistedPlaces.OrbitValuationBound Fm

abbrev AdmFC {eps : ℝ} (Fm : FamP eps) (C : ℝ) : Prop := TwistedPlaces.AdmFC Fm C

abbrev AdmF {eps : ℝ} (Fm : FamP eps) : Prop := TwistedPlaces.AdmF Fm

abbrev KudlaFamilyStatement {eps : ℝ} (Fm : FamP eps) : Prop := TwistedPlaces.KudlaFamilyStatement Fm

abbrev UniformExportStatement (eps : ℝ) : Prop := TwistedPlaces.UniformExportStatement eps

theorem stmtF_of_stmtU {eps : ℝ} (h : UniformExportStatement eps) (Fm : FamP eps) : KudlaFamilyStatement Fm := TwistedPlaces.stmtF_of_stmtU h Fm

end Formalism.MainNotions.ExportFamilies

end
