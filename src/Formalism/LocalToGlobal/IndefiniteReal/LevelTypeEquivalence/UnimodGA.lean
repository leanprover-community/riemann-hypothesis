module

public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.PeterssonNormOfUpLift
public import Formalism.LocalToGlobal.IndefiniteReal.HaarTransfer.UnimodP
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.NumFieldHosCountable
public import Formalism.PeriodIntegrals.ExplicitFormulaCounts.AdUnimod
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UJUnimod
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fin

variable {D : D7} {V : HSp D} (fr : UI.Frames D V)

def jf (x : (UI.instV fr).Gf) : GA D V := UI.brg fr (1, x)

theorem jf_isClosedEmbedding : Topology.IsClosedEmbedding (jf fr) := by
  haveI : T2Space (Matrix (Fin (UI.instV fr).n) (Fin (UI.instV fr).n) ℂ)ˣ :=
    Units.isEmbedding_embedProduct.t2Space
  haveI : T2Space (UI.instV fr).Ginf := inferInstance
  have hemb : Topology.IsEmbedding (fun x : (UI.instV fr).Gf => ((1 : (UI.instV fr).Ginf), x)) :=
    Function.LeftInverse.isEmbedding (f := Prod.snd) (fun _ => rfl) continuous_snd
      (continuous_const.prodMk continuous_id)
  have hcl : IsClosed (Set.range fun x : (UI.instV fr).Gf => ((1 : (UI.instV fr).Ginf), x)) := by
    have hr : (Set.range fun x : (UI.instV fr).Gf => ((1 : (UI.instV fr).Ginf), x)) =
        ({1} : Set (UI.instV fr).Ginf) ×ˢ Set.univ := by
      ext ⟨a, b⟩
      constructor
      · rintro ⟨y, hy⟩
        simp only [Prod.mk.injEq] at hy
        exact ⟨hy.1.symm, Set.mem_univ _⟩
      · rintro ⟨ha, -⟩
        have ha' : a = 1 := ha
        exact ⟨b, by rw [ha']⟩
    rw [hr]
    exact isClosed_singleton.prod isClosed_univ
  have h1 : Topology.IsClosedEmbedding
      (fun x : (UI.instV fr).Gf => ((1 : (UI.instV fr).Ginf), x)) := ⟨hemb, hcl⟩
  exact (UI.brg fr).toHomeomorph.isClosedEmbedding.comp h1

theorem gf_facts : T2Space (UI.instV fr).Gf ∧ LocallyCompactSpace (UI.instV fr).Gf ∧
    SecondCountableTopology (UI.instV fr).Gf := by
  obtain ⟨h1, h2, h3⟩ := G5.af_facts D.host.F
  obtain ⟨h1, h2, h3, h4, h5⟩ := G5.ha_facts (AF D.host.F) D.sp.cm.deg2 D.sp.cm.sig V.gram
  have he := jf_isClosedEmbedding fr
  exact ⟨he.isEmbedding.t2Space, he.locallyCompactSpace, he.isInducing.secondCountableTopology⟩

end Fin

theorem uJ_rightInv {n : ℕ} (ε : Fin n → Bool) (μ : Measure (Formalism.REAL.UJ ε)) (hμ : μ.IsHaarMeasure) :
    μ.IsMulRightInvariant := by
  have hR : (Formalism.REAL.muG ε).IsMulRightInvariant := unitary_unimodular_right_inv n ε
  rw [Measure.isMulLeftInvariant_eq_smul μ (Formalism.REAL.muG ε)]
  exact ⟨fun g => by rw [Measure.map_smul _ (continuous_mul_const g).aemeasurable,
    hR.map_mul_right_eq_self]⟩

theorem unimodGA_of_frames {D : D7} {V : HSp D} (fr : UI.Frames D V) : UnimodGA V := by
  obtain ⟨h1, h2, h3⟩ := G5.af_facts D.host.F
  obtain ⟨h1, h2, h3, h4, h5⟩ := G5.ha_facts (AF D.host.F) D.sp.cm.deg2 D.sp.cm.sig V.gram
  obtain ⟨g1, g2, g3⟩ := gf_facts fr
  have hinf : ∀ μ : Measure (UI.instV fr).Ginf, μ.IsHaarMeasure → μ.IsMulRightInvariant :=
    Leaf.Proofs.piStatement_holds (InfinitePlace D.host.F) (fun v => Formalism.REAL.UJ (fr.ε v))
      (fun v μ hμ => uJ_rightInv (fr.ε v) μ hμ)
  have hf : ∀ μ : Measure (UI.instV fr).Gf, μ.IsHaarMeasure → μ.IsMulRightInvariant :=
    fun μ hμ => adUnimod_closed (UI.instV fr) μ hμ
  have hprod := Leaf.Proofs.prodStatement_holds (UI.instV fr).Ginf (UI.instV fr).Gf hinf hf
  exact Leaf.Proofs.transferStatement_holds (UI.instV fr).GA (GA D V) (UI.brg fr) hprod

theorem unimodGA_holds {D : D7} (V : HSp D) : UnimodGA V :=
  unimodGA_of_frames (UI.frames_nonempty D V).some

end Formalism.IndefR.Eqv

end
