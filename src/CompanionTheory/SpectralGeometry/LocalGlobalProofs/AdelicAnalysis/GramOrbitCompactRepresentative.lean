module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompactPartClosedOrbit
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RationalGramAdelicCompactFiniteStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionRationalToAdelicStatement
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.Proper

theorem compact_gram_fibre :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
      IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      ∀ (n : ℕ) (X : Fin n → Fin M → E), (gramE σ J X).det ≠ 0 →
      ∀ Ω : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact Ω →
      ∃ C : Set (HA (AF F) σ J), IsCompact C ∧
        ∀ Y ∈ Ω, gramR (AF F) σ J Y = (gramE σ J X).map (inclR (AF F)) →
          ∃ c ∈ C, actW (AF F) σ J c (ratTup (AF F) X) = Y := by
  intro F E _ _ _ _ _ σ hσ M J hJ n X hX Ω hΩ
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := hlc
  haveI := hsc
  haveI := ht2
  obtain ⟨htg, hlcH, hscH, ht2H, -, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (AF F)
  haveI := htg
  haveI := hlcH
  haveI := hscH
  haveI := ht2H
  obtain ⟨-, hlcK, -, ht2K, -, -, -, -, -, hgram⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (AF F)
  haveI := hlcK
  haveI := ht2K
  obtain ⟨hcont, h1, hmul, hinv⟩ := hact n
  obtain ⟨-, hrat, -⟩ := GlobalTheory.T.rational_gram_adelic_compact_finite F E σ hσ M J hJ
  have hZ : IsClosed {Y : Fin n → Fin M → AF F ⊗[F] E |
      gramR (AF F) σ J Y = (gramE σ J X).map (inclR (AF F))} :=
    isClosed_eq (hgram n M J) continuous_const
  have hZx : ∀ Y : Fin n → Fin M → AF F ⊗[F] E,
      Y ∈ {Y : Fin n → Fin M → AF F ⊗[F] E |
        gramR (AF F) σ J Y = (gramE σ J X).map (inclR (AF F))} ↔
      ∃ g : HA (AF F) σ J, actW (AF F) σ J g (ratTup (AF F) X) = Y := by
    intro Y
    constructor
    · intro hY
      exact GlobalTheory.T.witt_extension_rational_to_adelic F E σ hσ M J hJ n X Y hX hY
    · rintro ⟨g, rfl⟩
      show gramR (AF F) σ J _ = _
      rw [hinv, hrat]
  obtain ⟨C, hC, hCY⟩ := GlobalTheory.CompanionTheory.Adelic.compact_part_closed_orbit (HA (AF F) σ J)
    (Fin n → Fin M → AF F ⊗[F] E) (fun g Y => actW (AF F) σ J g Y) hcont h1 hmul _
    (ratTup (AF F) X) hZ hZx Ω hΩ
  exact ⟨C, hC, fun Y hY hg => hCY Y hY hg⟩

end GlobalTheory.CompanionTheory.SW.Proper
