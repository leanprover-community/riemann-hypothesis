module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.FinSplit
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.CompDef, Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.ExistsEigenLift

-- ===== clump member: Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.CompDef =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.CompDef", "h": "module\n\npublic import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace PositivityTheory.ThK

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

def CompAtTriple : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v w, Formalism.UG.IsInertAt F E v w → v ∉ X.T →
      augAt om' v ≠ SB _ ∧
      (∀ N : Submodule ℂ (_ → ℂ), augAt om' v ≤ N → N ≤ SB _ → (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ N, ∀ φ₁ ∈ SB _,
        Acts (evFin F v) (om' (1, h)) φ φ₁ → φ₁ ∈ N) → N = augAt om' v ∨ N = SB _) ∧
      ∃ p : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (((Fin a' × Fin (a + a') → Fv F v) → ℂ) ⧸ augAt om' v),
        (SB _).map p = (SB _).map (augAt om' v).mkQ ∧ augAt om v ≤ LinearMap.ker p ∧
        ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ' ∈ SB _, ∀ φ₁ ∈ SB _, ∀ φ₁' ∈ SB _,
          Acts (evFin F v) (om (1, h)) φ φ₁ → Acts (evFin F v) (om' (1, h)) φ' φ₁' →
          p φ = (augAt om' v).mkQ φ' → p φ₁ = (augAt om' v).mkQ φ₁'

end PositivityTheory.ThK
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.CompDef =====

-- ===== clump member: Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.ExistsEigenLift =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.ExistsEigenLift", "h": "module\n\npublic import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.CompDef\npublic import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.FinSplit\npublic import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Etale.Weakly\nimport Mathlib.RingTheory.Finiteness.ModuleFinitePresentation\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.TotallySplit\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace PositivityTheory.ThK

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

theorem one_mem_UAt (X : Spc F E n) (v : Pl F) : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := fun u _ => by
  have : mat (1 : UA σ X.J) = 1 := rfl
  rw [this, sub_self, smul_zero]

theorem mul_mem_UAt {X : Spc F E n} {v : Pl F} {g h : UA σ X.J} (hg : g ∈ UAt σ X (evFin F v)) (hh : h ∈ UAt σ X (evFin F v)) :
    g * h ∈ UAt σ X (evFin F v) := fun u hu => by
  have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by
    have : mat (g * h) = mat g * mat h := rfl
    rw [this, sub_mul, one_mul]; abel
  rw [e, smul_add, ← Matrix.smul_mul, hg u hu, hh u hu, Matrix.zero_mul, add_zero]

theorem mat_inv_mul {X : Spc F E n} (g : UA σ X.J) : mat g⁻¹ * mat g = 1 := by
  have : mat (g⁻¹ * g) = mat g⁻¹ * mat g := rfl
  rw [← this, inv_mul_cancel]; rfl

theorem inv_mem_UAt {X : Spc F E n} {v : Pl F} {g : UA σ X.J} (hg : g ∈ UAt σ X (evFin F v)) :
    g⁻¹ ∈ UAt σ X (evFin F v) := fun u hu => by
  have e : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by rw [mul_sub, mat_inv_mul, mul_one, neg_sub]
  rw [e, smul_neg, ← Matrix.mul_smul, hg u hu, Matrix.mul_zero, neg_zero]

variable (σ) in
def KSub (W : Spc F E d) (v : Pl F) : Subgroup (UA σ W.J) where
  carrier := KAt σ W v
  one_mem' := ⟨one_mem_UAt W v, fun y hy => by
    have : mat (1 : UA σ W.J) = 1 := rfl
    rw [inv_one, this, Matrix.one_mulVec]; exact ⟨hy, hy⟩⟩
  mul_mem' := fun {g h} hg hh => ⟨mul_mem_UAt hg.1 hh.1, fun y hy => by
    have e1 : mat (g * h) = mat g * mat h := rfl
    have e2 : mat (h⁻¹ * g⁻¹) = mat h⁻¹ * mat g⁻¹ := rfl
    rw [mul_inv_rev, e1, e2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact ⟨(hg.2 _ (hh.2 y hy).1).1, (hh.2 _ (hg.2 y hy).2).2⟩⟩
  inv_mem' := fun {g} hg => ⟨inv_mem_UAt hg.1, fun y hy => by
    rw [inv_inv]; exact ⟨(hg.2 y hy).2, (hg.2 y hy).1⟩⟩

section Loc

variable {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl F}
  {ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (AE F E) → Module.End ℂ (Fn F n d v)}

theorem IsLocRep.mulW (L : IsLocRep M ψ om v ω ρ) {h h' : UA σ W.J} (hh : h ∈ UAt σ W (evFin F v)) (hh' : h' ∈ UAt σ W (evFin F v))
    {φ} (hφ : φ ∈ SB _) : ω (1, h * h') φ = ω (1, h) (ω (1, h') φ) := by
  simpa using L.mul 1 (one_mem_UAt X v) h hh 1 (one_mem_UAt X v) h' hh' φ hφ

def IsLocRep.onK (L : IsLocRep M ψ om v ω ρ) : KSub σ W v →* Module.End ℂ (SB (Fin n × Fin d → Fv F v)) where
  toFun k := (ω (1, k.1)).restrict fun φ hφ => L.pres 1 (one_mem_UAt X v) k.1 k.2.1 φ hφ
  map_one' := LinearMap.ext fun φ => Subtype.ext (L.one φ φ.2)
  map_mul' a b := LinearMap.ext fun φ => Subtype.ext (L.mulW a.2.1 b.2.1 φ.2)

end Loc

end PositivityTheory.ThK
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.ExistsEigenLift =====
