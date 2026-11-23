module

public import Formalism.LocalToGlobal.Columns.Adelic
public import Formalism.LocalToGlobal.Divisibility.Tuples
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.Columns.AdelicLemmas
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep Matrix
open Formalism.L2.Theta GlobalTheory.Mem.Th Filter Topology MeasureTheory
open GlobalTheory.Mem.ColAd GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.TC
attribute [local instance] GlobalTheory.Mem.Col2.starE

noncomputable section

open Formalism.UG Formalism.MainNotions

namespace GlobalTheory.Mem.ColAd.LevGrp

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) {n : ℕ} [NeZero n] {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem decoRaw_mul_levelIwahori_reduction (g z : GL (Fin n) (AfE F E)) (hz : z ∈ J0 hc n ST) :
    decoRaw ST SG (g * z) = (decoRaw ST SG g).act 1 (redG hc n ST SG ⟨z, hz⟩)⁻¹ := by
  have h := decoRaw_rawSm hc ST SG 1 (⟨z, hz⟩⁻¹ : J0 hc n ST) g
  rw [map_one, map_inv] at h
  have e : Formalism.UG.bc (iA F E) ((1 : URat hc n) : GL (Fin n) E) * g *
      (((⟨z, hz⟩⁻¹ : J0 hc n ST) : J0 hc n ST) : GL (Fin n) (AfE F E))⁻¹ = g * z := by
    simp
  rw [e] at h
  exact h

end Gen


attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) [NeZero n]


end GlobalTheory.Mem.ColAd.LevGrp

namespace GlobalTheory.Mem.Col2.TC

open GlobalTheory.Mem.ColAd.LevGrp

end GlobalTheory.Mem.Col2.TC
