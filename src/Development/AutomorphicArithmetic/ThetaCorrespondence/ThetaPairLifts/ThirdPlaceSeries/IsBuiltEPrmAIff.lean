module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithAtProperty
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AddLargeBaseCoreSlot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.LiteralAutomorphy
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL} {S : SExt} {Γ : GeoP} {A : AtP}
def builtA_drop_alt {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {c : V4.Core K (w.st Z) f T}
    (b : Built (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N A) S Γ).s K w Z c) : Built (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K w Z c :=
  { b with nx := ⟨b.nx.1, b.nx.2.1⟩ }
def builtExtendByAutomorphy {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {c : V4.Core K (w.st Z) f T}
    (b : Built (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K w Z c) (a : A K B f T) : Built (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N A) S Γ).s K w Z c :=
  { b with nx := ⟨b.nx.1, b.nx.2, PLift.up a⟩ }
theorem isBuiltE_extensionWithAtProperty_iff (K X f T c) :
    IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N A) S Γ).s K X f T c ↔ IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K X f T c ∧ A K X.B f T := by
  constructor
  · rintro ⟨w, Z, c', ⟨b, hb⟩, he⟩
    exact ⟨⟨w, Z, c', ⟨_root_.GlobalTheory.Mem.LiteralAutomorphy.builtA_drop_alt b, hb⟩, he⟩, b.nx.2.2.down⟩
  · rintro ⟨⟨w, Z, c', ⟨b, hb⟩, he⟩, a⟩
    exact ⟨w, Z, c', ⟨_root_.GlobalTheory.Mem.LiteralAutomorphy.builtExtendByAutomorphy b a, hb⟩, he⟩
theorem isGoodE_extensionWithAtProperty_iff (K X f T c) :
    IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N A) S Γ).s K X f T c ↔ IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K X f T c ∧ A K X.B f T := by
  constructor
  · rintro ⟨w, Z, c', ⟨⟨b, hb⟩, g⟩, he⟩
    exact ⟨⟨w, Z, c', ⟨⟨_root_.GlobalTheory.Mem.LiteralAutomorphy.builtA_drop_alt b, hb⟩, g⟩, he⟩, b.nx.2.2.down⟩
  · rintro ⟨⟨w, Z, c', ⟨⟨b, hb⟩, g⟩, he⟩, a⟩
    exact ⟨w, Z, c', ⟨⟨_root_.GlobalTheory.Mem.LiteralAutomorphy.builtExtendByAutomorphy b a, hb⟩, g⟩, he⟩
theorem memberE_extensionWithAtProperty_of_memberE : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP) (A : AtP), EvLgG A →
    MemberE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s → MemberE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N A) S Γ).s := by
  intro hL N S Γ A hA ⟨hB, h1, hE, h2⟩
  refine ⟨hB, ?_, ?_, ?_⟩
  · have h := Step.and (KP := KPx) h1 (Step.of_evLgG (p := fun _ B _ T => T = TwDat.untw B T.pl) hA)
    refine EvG.imp h fun K _ _ _ _ H => H.imp fun B f T _ G k u v => ?_
    obtain ⟨⟨C, W, V, S, N, Gs, c, q⟩, a⟩ := G k u v
    exact ⟨C, W, V, S, N, Gs, c, (_root_.GlobalTheory.Mem.LiteralAutomorphy.isBuiltE_extensionWithAtProperty_iff K ⟨B, C, W, V, S, N, Gs⟩ f T c).2 ⟨q, a⟩⟩
  · exact EvG.imp hE fun K _ _ _ _ H => H.imp fun B f T _ G k u C W V S N Gs c q =>
      G k u C W V S N Gs c ((_root_.GlobalTheory.Mem.LiteralAutomorphy.isBuiltE_extensionWithAtProperty_iff K ⟨B, C, W, V, S, N, Gs⟩ f T c).1 q).1
  · have hR : LargeBaseConditionG KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (fun K X f T _ => A K X.B f T) :=
      EvG.imp hA fun K _ _ _ _ H => H.imp fun B f T _ a _ C W V S N Gs c _ => a
    have h2' := SecondG.sAnd_of_largeBase KPx _ _ _ hB hR h2
    refine EvG.imp h2' fun K _ _ _ _ H => H.imp fun B f T _ G k u C W V S N Gs c q e Av S₂ hS₂ => ?_
    obtain ⟨B', f', T', a1, a2, a3, a4, a5, C', W', V', S', N', G', c', q', tw, g', a⟩ :=
      G k u C W V S N Gs c ((_root_.GlobalTheory.Mem.LiteralAutomorphy.isBuiltE_extensionWithAtProperty_iff K ⟨B, C, W, V, S, N, Gs⟩ f T c).1 q).1 e Av S₂ hS₂
    exact ⟨B', f', T', a1, a2, a3, a4, a5, C', W', V', S', N', G', c',
      (_root_.GlobalTheory.Mem.LiteralAutomorphy.isBuiltE_extensionWithAtProperty_iff K ⟨B', C', W', V', S', N', G'⟩ f' T' c').2 ⟨q', a⟩, tw,
      (_root_.GlobalTheory.Mem.LiteralAutomorphy.isGoodE_extensionWithAtProperty_iff K ⟨B', C', W', V', S', N', G'⟩ f' T' c').2 ⟨g', a⟩⟩
end GlobalTheory.Mem.LiteralAutomorphy
end
