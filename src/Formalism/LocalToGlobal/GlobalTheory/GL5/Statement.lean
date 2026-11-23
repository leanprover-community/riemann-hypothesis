module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions
open scoped TensorProduct

def FrameTied (D : D7) (Lv : LevelData D) : Prop :=
  letI := D.host.cmStar
  ∀ (u : D.what₂.Word) (i : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F))
    (h : ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) (t : Fin D.R.k → v.adicCompletion D.host.F),
    (∃ y ∈ Formalism.L2.Herm.locL (F := D.host.F) (E := D.host.E) v (Lv u).Lb,
        ∀ a, ((Lv u).splitG i v h (y a)).1 = t a) ↔
      ∀ a, ((((Lv u).frG i v h)⁻¹ : GL (Fin D.R.k) (v.adicCompletion D.host.F)) :
        Matrix (Fin D.R.k) (Fin D.R.k) (v.adicCompletion D.host.F)).mulVec t a ∈
          v.adicCompletionIntegers D.host.F

def VolRatioTrue (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (P, Q)) → 3 ≤ W.rank →
    ∀ s : Bool, (if s then 1 ≤ P else 1 ≤ Q) →
    ∃ x : W.V, W.hT x x = (if s then 1 else -1) ∧
      ∃ (W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V),
        HSpace.IsIsomEmb W' W ι ∧ LinearMap.range ι = LinearMap.ker (W.hT x) ∧ W'.SigOK ∧
        (∀ τ, W'.sig τ = (if s then (P - 1, Q) else (P, Q - 1))) ∧
        ∀ (μ : Measure (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.sp.cm.sig W.gram))
          (𝓕 : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.sp.cm.sig W.gram))
          (μ' : Measure (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.sp.cm.sig W'.gram))
          (𝓕' : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.sp.cm.sig W'.gram)),
          Formalism.MainNotions.StandardLattice.IsVolMeas D W P Q μ →
          IsFundamentalDomain (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ →
          Formalism.MainNotions.StandardLattice.IsVolMeas D W' (if s then P - 1 else P) (if s then Q else Q - 1) μ' →
          IsFundamentalDomain (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.sp.cm.sig W'.gram) 𝓕' μ' →
          (μ 𝓕).toReal / (μ' 𝓕').toReal = Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E W.rank

def LandherrHasse (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ W : HSpace D.host.E, W.SigOK → (∀ τ, W.sig τ = (W.rank, 0)) →
    ∃ b : Fin W.rank → W.V, LinearIndependent D.host.E b ∧
      ∀ a c, W.hT (b a) (b c) = if a = c then 1 else 0

def GenusMassStd (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ W : HSpace D.host.E, W.SigOK → (∀ τ, W.sig τ = (W.rank, 0)) →
    Formalism.HermitianLatticesTheory.mass W.hT W.L0 = Formalism.MainNotions.StandardLattice.massI D W.rank

def Link4p : Prop := ∀ (D : D7) (Lv : LevelData D), Formalism.MainNotions.StandardLattice.Conclusion4p D Lv

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

end
