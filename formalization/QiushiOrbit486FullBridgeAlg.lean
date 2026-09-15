
-- Auto-generated orbit 486 algebraic full-bridge module
-- Conditional bridge: algebraic full row premises imply reduced RootHolds.

import Mathlib
import QiushiOrbit486Tree

set_option maxHeartbeats 6000000
set_option maxRecDepth 5000

open BigOperators Finset
namespace QiushiMatmul

def evalSet127_486 (s : Finset (Fin 127)) (X : Fin 127 → Int) : Int := Finset.sum s X

def livePoint486 : Fin 40 → Fin 127 := fun i =>
  match i.val with
  | 0 => ⟨1, by decide⟩
  | 1 => ⟨2, by decide⟩
  | 2 => ⟨3, by decide⟩
  | 3 => ⟨4, by decide⟩
  | 4 => ⟨5, by decide⟩
  | 5 => ⟨6, by decide⟩
  | 6 => ⟨7, by decide⟩
  | 7 => ⟨8, by decide⟩
  | 8 => ⟨9, by decide⟩
  | 9 => ⟨15, by decide⟩
  | 10 => ⟨17, by decide⟩
  | 11 => ⟨19, by decide⟩
  | 12 => ⟨22, by decide⟩
  | 13 => ⟨23, by decide⟩
  | 14 => ⟨25, by decide⟩
  | 15 => ⟨28, by decide⟩
  | 16 => ⟨29, by decide⟩
  | 17 => ⟨31, by decide⟩
  | 18 => ⟨33, by decide⟩
  | 19 => ⟨35, by decide⟩
  | 20 => ⟨38, by decide⟩
  | 21 => ⟨39, by decide⟩
  | 22 => ⟨41, by decide⟩
  | 23 => ⟨44, by decide⟩
  | 24 => ⟨45, by decide⟩
  | 25 => ⟨48, by decide⟩
  | 26 => ⟨63, by decide⟩
  | 27 => ⟨64, by decide⟩
  | 28 => ⟨67, by decide⟩
  | 29 => ⟨79, by decide⟩
  | 30 => ⟨82, by decide⟩
  | 31 => ⟨83, by decide⟩
  | 32 => ⟨85, by decide⟩
  | 33 => ⟨95, by decide⟩
  | 34 => ⟨98, by decide⟩
  | 35 => ⟨99, by decide⟩
  | 36 => ⟨101, by decide⟩
  | 37 => ⟨119, by decide⟩
  | 38 => ⟨120, by decide⟩
  | 39 => ⟨125, by decide⟩
  | _ => ⟨0, by decide⟩

def deadPoint486 : Fin 87 → Fin 127 := fun i =>
  match i.val with
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨10, by decide⟩
  | 2 => ⟨11, by decide⟩
  | 3 => ⟨12, by decide⟩
  | 4 => ⟨13, by decide⟩
  | 5 => ⟨14, by decide⟩
  | 6 => ⟨16, by decide⟩
  | 7 => ⟨18, by decide⟩
  | 8 => ⟨20, by decide⟩
  | 9 => ⟨21, by decide⟩
  | 10 => ⟨24, by decide⟩
  | 11 => ⟨26, by decide⟩
  | 12 => ⟨27, by decide⟩
  | 13 => ⟨30, by decide⟩
  | 14 => ⟨32, by decide⟩
  | 15 => ⟨34, by decide⟩
  | 16 => ⟨36, by decide⟩
  | 17 => ⟨37, by decide⟩
  | 18 => ⟨40, by decide⟩
  | 19 => ⟨42, by decide⟩
  | 20 => ⟨43, by decide⟩
  | 21 => ⟨46, by decide⟩
  | 22 => ⟨47, by decide⟩
  | 23 => ⟨49, by decide⟩
  | 24 => ⟨50, by decide⟩
  | 25 => ⟨51, by decide⟩
  | 26 => ⟨52, by decide⟩
  | 27 => ⟨53, by decide⟩
  | 28 => ⟨54, by decide⟩
  | 29 => ⟨55, by decide⟩
  | 30 => ⟨56, by decide⟩
  | 31 => ⟨57, by decide⟩
  | 32 => ⟨58, by decide⟩
  | 33 => ⟨59, by decide⟩
  | 34 => ⟨60, by decide⟩
  | 35 => ⟨61, by decide⟩
  | 36 => ⟨62, by decide⟩
  | 37 => ⟨65, by decide⟩
  | 38 => ⟨66, by decide⟩
  | 39 => ⟨68, by decide⟩
  | 40 => ⟨69, by decide⟩
  | 41 => ⟨70, by decide⟩
  | 42 => ⟨71, by decide⟩
  | 43 => ⟨72, by decide⟩
  | 44 => ⟨73, by decide⟩
  | 45 => ⟨74, by decide⟩
  | 46 => ⟨75, by decide⟩
  | 47 => ⟨76, by decide⟩
  | 48 => ⟨77, by decide⟩
  | 49 => ⟨78, by decide⟩
  | 50 => ⟨80, by decide⟩
  | 51 => ⟨81, by decide⟩
  | 52 => ⟨84, by decide⟩
  | 53 => ⟨86, by decide⟩
  | 54 => ⟨87, by decide⟩
  | 55 => ⟨88, by decide⟩
  | 56 => ⟨89, by decide⟩
  | 57 => ⟨90, by decide⟩
  | 58 => ⟨91, by decide⟩
  | 59 => ⟨92, by decide⟩
  | 60 => ⟨93, by decide⟩
  | 61 => ⟨94, by decide⟩
  | 62 => ⟨96, by decide⟩
  | 63 => ⟨97, by decide⟩
  | 64 => ⟨100, by decide⟩
  | 65 => ⟨102, by decide⟩
  | 66 => ⟨103, by decide⟩
  | 67 => ⟨104, by decide⟩
  | 68 => ⟨105, by decide⟩
  | 69 => ⟨106, by decide⟩
  | 70 => ⟨107, by decide⟩
  | 71 => ⟨108, by decide⟩
  | 72 => ⟨109, by decide⟩
  | 73 => ⟨110, by decide⟩
  | 74 => ⟨111, by decide⟩
  | 75 => ⟨112, by decide⟩
  | 76 => ⟨113, by decide⟩
  | 77 => ⟨114, by decide⟩
  | 78 => ⟨115, by decide⟩
  | 79 => ⟨116, by decide⟩
  | 80 => ⟨117, by decide⟩
  | 81 => ⟨118, by decide⟩
  | 82 => ⟨121, by decide⟩
  | 83 => ⟨122, by decide⟩
  | 84 => ⟨123, by decide⟩
  | 85 => ⟨124, by decide⟩
  | 86 => ⟨126, by decide⟩
  | _ => ⟨0, by decide⟩

def deadEmb486 : Fin 87 ↪ Fin 127 :=
  ⟨deadPoint486, by decide⟩

private def extraMaskBlock486_00 (off : Nat) : Finset (Fin 127) :=
  match off with
  | 0 => (∅ : Finset (Fin 127))
  | 1 => (∅ : Finset (Fin 127))
  | 2 => (∅ : Finset (Fin 127))
  | 3 => (∅ : Finset (Fin 127))
  | 4 => ({⟨103, by decide⟩} : Finset (Fin 127))
  | 5 => ({⟨106, by decide⟩} : Finset (Fin 127))
  | 6 => ({⟨0, by decide⟩, ⟨126, by decide⟩} : Finset (Fin 127))
  | 7 => ({⟨0, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩} : Finset (Fin 127))
  | 8 => ({⟨0, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩} : Finset (Fin 127))
  | 9 => ({⟨0, by decide⟩, ⟨10, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩} : Finset (Fin 127))
  | 10 => ({⟨16, by decide⟩, ⟨84, by decide⟩} : Finset (Fin 127))
  | 11 => ({⟨0, by decide⟩, ⟨18, by decide⟩, ⟨21, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨80, by decide⟩, ⟨84, by decide⟩} : Finset (Fin 127))
  | 12 => ({⟨0, by decide⟩, ⟨16, by decide⟩, ⟨20, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨81, by decide⟩, ⟨86, by decide⟩} : Finset (Fin 127))
  | 13 => ({⟨0, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨96, by decide⟩, ⟨100, by decide⟩} : Finset (Fin 127))
  | 14 => ({⟨0, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨68, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩, ⟨115, by decide⟩, ⟨116, by decide⟩} : Finset (Fin 127))
  | 15 => ({⟨47, by decide⟩, ⟨55, by decide⟩, ⟨71, by decide⟩, ⟨87, by decide⟩, ⟨103, by decide⟩, ⟨111, by decide⟩} : Finset (Fin 127))
  | 16 => ({⟨47, by decide⟩, ⟨56, by decide⟩, ⟨71, by decide⟩, ⟨94, by decide⟩, ⟨110, by decide⟩, ⟨112, by decide⟩} : Finset (Fin 127))
  | 17 => ({⟨11, by decide⟩, ⟨26, by decide⟩, ⟨52, by decide⟩, ⟨56, by decide⟩, ⟨76, by decide⟩, ⟨89, by decide⟩, ⟨110, by decide⟩, ⟨115, by decide⟩} : Finset (Fin 127))
  | 18 => ({⟨47, by decide⟩, ⟨56, by decide⟩, ⟨72, by decide⟩, ⟨92, by decide⟩, ⟨108, by decide⟩, ⟨111, by decide⟩} : Finset (Fin 127))
  | 19 => ({⟨47, by decide⟩, ⟨55, by decide⟩, ⟨72, by decide⟩, ⟨90, by decide⟩, ⟨106, by decide⟩, ⟨112, by decide⟩} : Finset (Fin 127))
  | 20 => ({⟨0, by decide⟩, ⟨40, by decide⟩, ⟨46, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨121, by decide⟩, ⟨122, by decide⟩, ⟨123, by decide⟩, ⟨124, by decide⟩} : Finset (Fin 127))
  | 21 => ({⟨0, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨80, by decide⟩, ⟨86, by decide⟩, ⟨121, by decide⟩, ⟨122, by decide⟩, ⟨123, by decide⟩, ⟨124, by decide⟩} : Finset (Fin 127))
  | 22 => ({⟨0, by decide⟩, ⟨24, by decide⟩, ⟨30, by decide⟩, ⟨97, by decide⟩, ⟨100, by decide⟩, ⟨121, by decide⟩, ⟨122, by decide⟩, ⟨123, by decide⟩, ⟨124, by decide⟩} : Finset (Fin 127))
  | 23 => ({⟨42, by decide⟩, ⟨84, by decide⟩} : Finset (Fin 127))
  | 24 => ({⟨26, by decide⟩, ⟨100, by decide⟩} : Finset (Fin 127))
  | 25 => ({⟨0, by decide⟩, ⟨47, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨126, by decide⟩} : Finset (Fin 127))
  | 26 => ({⟨13, by decide⟩, ⟨18, by decide⟩, ⟨24, by decide⟩, ⟨37, by decide⟩, ⟨43, by decide⟩, ⟨52, by decide⟩, ⟨58, by decide⟩, ⟨62, by decide⟩, ⟨68, by decide⟩, ⟨74, by decide⟩, ⟨78, by decide⟩, ⟨81, by decide⟩, ⟨87, by decide⟩, ⟨91, by decide⟩, ⟨102, by decide⟩, ⟨104, by decide⟩, ⟨108, by decide⟩, ⟨111, by decide⟩, ⟨115, by decide⟩, ⟨121, by decide⟩} : Finset (Fin 127))
  | 27 => ({⟨14, by decide⟩, ⟨20, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨42, by decide⟩, ⟨51, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨68, by decide⟩, ⟨73, by decide⟩, ⟨78, by decide⟩, ⟨84, by decide⟩, ⟨89, by decide⟩, ⟨94, by decide⟩, ⟨96, by decide⟩, ⟨106, by decide⟩, ⟨109, by decide⟩, ⟨112, by decide⟩, ⟨115, by decide⟩, ⟨122, by decide⟩} : Finset (Fin 127))
  | 28 => ({⟨14, by decide⟩, ⟨16, by decide⟩, ⟨26, by decide⟩, ⟨36, by decide⟩, ⟨46, by decide⟩, ⟨51, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨68, by decide⟩, ⟨73, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩, ⟨90, by decide⟩, ⟨93, by decide⟩, ⟨100, by decide⟩, ⟨105, by decide⟩, ⟨110, by decide⟩, ⟨112, by decide⟩, ⟨115, by decide⟩, ⟨122, by decide⟩} : Finset (Fin 127))
  | 29 => ({⟨11, by decide⟩, ⟨26, by decide⟩, ⟨42, by decide⟩, ⟨47, by decide⟩, ⟨52, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨65, by decide⟩, ⟨70, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨84, by decide⟩, ⟨88, by decide⟩, ⟨91, by decide⟩, ⟨100, by decide⟩, ⟨104, by decide⟩, ⟨107, by decide⟩, ⟨113, by decide⟩, ⟨118, by decide⟩, ⟨122, by decide⟩} : Finset (Fin 127))
  | 30 => ({⟨10, by decide⟩, ⟨21, by decide⟩, ⟨30, by decide⟩, ⟨36, by decide⟩, ⟨43, by decide⟩, ⟨50, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨69, by decide⟩, ⟨76, by decide⟩, ⟨78, by decide⟩, ⟨81, by decide⟩, ⟨88, by decide⟩, ⟨90, by decide⟩, ⟨96, by decide⟩, ⟨103, by decide⟩, ⟨105, by decide⟩, ⟨116, by decide⟩, ⟨118, by decide⟩, ⟨123, by decide⟩} : Finset (Fin 127))
  | 31 => ({⟨10, by decide⟩, ⟨20, by decide⟩, ⟨27, by decide⟩, ⟨37, by decide⟩, ⟨46, by decide⟩, ⟨50, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨69, by decide⟩, ⟨76, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩, ⟨87, by decide⟩, ⟨89, by decide⟩, ⟨97, by decide⟩, ⟨104, by decide⟩, ⟨106, by decide⟩, ⟨116, by decide⟩, ⟨118, by decide⟩, ⟨123, by decide⟩} : Finset (Fin 127))
  | 32 => ({⟨11, by decide⟩, ⟨21, by decide⟩, ⟨27, by decide⟩, ⟨32, by decide⟩, ⟨42, by decide⟩, ⟨54, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨65, by decide⟩, ⟨71, by decide⟩, ⟨77, by decide⟩, ⟨81, by decide⟩, ⟨87, by decide⟩, ⟨93, by decide⟩, ⟨100, by decide⟩, ⟨104, by decide⟩, ⟨110, by decide⟩, ⟨114, by decide⟩, ⟨116, by decide⟩, ⟨126, by decide⟩} : Finset (Fin 127))
  | 33 => ({⟨0, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨24, by decide⟩, ⟨30, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨40, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨97, by decide⟩, ⟨100, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨109, by decide⟩, ⟨110, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩, ⟨117, by decide⟩, ⟨118, by decide⟩, ⟨121, by decide⟩, ⟨122, by decide⟩, ⟨123, by decide⟩, ⟨124, by decide⟩} : Finset (Fin 127))
  | 34 => ({⟨10, by decide⟩, ⟨11, by decide⟩, ⟨14, by decide⟩, ⟨18, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩, ⟨110, by decide⟩, ⟨111, by decide⟩, ⟨114, by decide⟩, ⟨115, by decide⟩, ⟨118, by decide⟩, ⟨122, by decide⟩, ⟨123, by decide⟩, ⟨126, by decide⟩} : Finset (Fin 127))
  | 35 => (∅ : Finset (Fin 127))
  | 36 => ({⟨34, by decide⟩, ⟨40, by decide⟩} : Finset (Fin 127))
  | 37 => ({⟨0, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩} : Finset (Fin 127))
  | 38 => ({⟨20, by decide⟩, ⟨80, by decide⟩} : Finset (Fin 127))
  | 39 => ({⟨36, by decide⟩, ⟨96, by decide⟩} : Finset (Fin 127))
  | _ => ∅

private def extraMaskBlock486_01 (off : Nat) : Finset (Fin 127) :=
  match off with
  | 0 => ({⟨0, by decide⟩, ⟨32, by decide⟩, ⟨36, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨97, by decide⟩, ⟨102, by decide⟩} : Finset (Fin 127))
  | 1 => ({⟨50, by decide⟩, ⟨57, by decide⟩, ⟨71, by decide⟩, ⟨94, by decide⟩, ⟨100, by decide⟩, ⟨107, by decide⟩, ⟨113, by decide⟩, ⟨122, by decide⟩} : Finset (Fin 127))
  | 2 => ({⟨27, by decide⟩, ⟨51, by decide⟩, ⟨59, by decide⟩, ⟨71, by decide⟩, ⟨91, by decide⟩, ⟨103, by decide⟩, ⟨115, by decide⟩, ⟨123, by decide⟩} : Finset (Fin 127))
  | 3 => ({⟨30, by decide⟩, ⟨52, by decide⟩, ⟨60, by decide⟩, ⟨72, by decide⟩, ⟨93, by decide⟩, ⟨106, by decide⟩, ⟨115, by decide⟩, ⟨123, by decide⟩} : Finset (Fin 127))
  | 4 => ({⟨40, by decide⟩, ⟨51, by decide⟩, ⟨60, by decide⟩, ⟨72, by decide⟩, ⟨92, by decide⟩, ⟨104, by decide⟩, ⟨115, by decide⟩, ⟨124, by decide⟩} : Finset (Fin 127))
  | 5 => ({⟨42, by decide⟩, ⟨52, by decide⟩, ⟨59, by decide⟩, ⟨71, by decide⟩, ⟨94, by decide⟩, ⟨105, by decide⟩, ⟨115, by decide⟩, ⟨124, by decide⟩} : Finset (Fin 127))
  | 6 => ({⟨16, by decide⟩, ⟨20, by decide⟩, ⟨52, by decide⟩, ⟨66, by decide⟩, ⟨70, by decide⟩, ⟨81, by decide⟩, ⟨102, by decide⟩, ⟨113, by decide⟩, ⟨117, by decide⟩} : Finset (Fin 127))
  | 7 => ({⟨10, by decide⟩, ⟨11, by decide⟩, ⟨20, by decide⟩, ⟨24, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨56, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨72, by decide⟩, ⟨77, by decide⟩, ⟨86, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨97, by decide⟩, ⟨100, by decide⟩, ⟨104, by decide⟩, ⟨109, by decide⟩, ⟨111, by decide⟩, ⟨118, by decide⟩, ⟨122, by decide⟩, ⟨123, by decide⟩} : Finset (Fin 127))
  | 8 => ({⟨12, by decide⟩, ⟨24, by decide⟩, ⟨40, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨56, by decide⟩, ⟨60, by decide⟩, ⟨66, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨77, by decide⟩, ⟨86, by decide⟩, ⟨89, by decide⟩, ⟨93, by decide⟩, ⟨102, by decide⟩, ⟨105, by decide⟩, ⟨109, by decide⟩, ⟨114, by decide⟩, ⟨118, by decide⟩, ⟨121, by decide⟩} : Finset (Fin 127))
  | 9 => ({⟨11, by decide⟩, ⟨13, by decide⟩, ⟨27, by decide⟩, ⟨43, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨81, by decide⟩, ⟨91, by decide⟩, ⟨93, by decide⟩, ⟨97, by decide⟩, ⟨107, by decide⟩, ⟨109, by decide⟩, ⟨111, by decide⟩, ⟨113, by decide⟩, ⟨123, by decide⟩} : Finset (Fin 127))
  | 10 => ({⟨11, by decide⟩, ⟨16, by decide⟩, ⟨26, by decide⟩, ⟨37, by decide⟩, ⟨43, by decide⟩, ⟨54, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨65, by decide⟩, ⟨71, by decide⟩, ⟨77, by decide⟩, ⟨84, by decide⟩, ⟨88, by decide⟩, ⟨94, by decide⟩, ⟨97, by decide⟩, ⟨103, by decide⟩, ⟨109, by decide⟩, ⟨114, by decide⟩, ⟨116, by decide⟩, ⟨126, by decide⟩} : Finset (Fin 127))
  | 11 => ({⟨0, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨21, by decide⟩, ⟨24, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨97, by decide⟩, ⟨100, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨113, by decide⟩, ⟨114, by decide⟩, ⟨115, by decide⟩, ⟨116, by decide⟩, ⟨121, by decide⟩, ⟨122, by decide⟩, ⟨123, by decide⟩, ⟨124, by decide⟩} : Finset (Fin 127))
  | 12 => ({⟨0, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨24, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨37, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩, ⟨86, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨97, by decide⟩, ⟨100, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨109, by decide⟩, ⟨110, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩, ⟨117, by decide⟩, ⟨118, by decide⟩, ⟨121, by decide⟩, ⟨122, by decide⟩, ⟨123, by decide⟩, ⟨124, by decide⟩} : Finset (Fin 127))
  | 13 => ({⟨0, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨84, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩, ⟨110, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩, ⟨113, by decide⟩, ⟨114, by decide⟩, ⟨123, by decide⟩, ⟨124, by decide⟩, ⟨126, by decide⟩} : Finset (Fin 127))
  | 14 => ({⟨87, by decide⟩} : Finset (Fin 127))
  | 15 => ({⟨18, by decide⟩, ⟨24, by decide⟩} : Finset (Fin 127))
  | 16 => ({⟨0, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩} : Finset (Fin 127))
  | 17 => ({⟨21, by decide⟩, ⟨27, by decide⟩} : Finset (Fin 127))
  | 18 => ({⟨34, by decide⟩, ⟨102, by decide⟩} : Finset (Fin 127))
  | 19 => ({⟨49, by decide⟩, ⟨57, by decide⟩, ⟨65, by decide⟩, ⟨73, by decide⟩, ⟨87, by decide⟩, ⟨97, by decide⟩, ⟨105, by decide⟩, ⟨111, by decide⟩} : Finset (Fin 127))
  | 20 => ({⟨49, by decide⟩, ⟨57, by decide⟩, ⟨66, by decide⟩, ⟨74, by decide⟩, ⟨80, by decide⟩, ⟨88, by decide⟩, ⟨106, by decide⟩, ⟨112, by decide⟩} : Finset (Fin 127))
  | 21 => ({⟨50, by decide⟩, ⟨57, by decide⟩, ⟨72, by decide⟩, ⟨86, by decide⟩, ⟨93, by decide⟩, ⟨108, by decide⟩, ⟨114, by decide⟩, ⟨121, by decide⟩} : Finset (Fin 127))
  | 22 => ({⟨0, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨96, by decide⟩, ⟨102, by decide⟩, ⟨121, by decide⟩, ⟨122, by decide⟩, ⟨123, by decide⟩, ⟨124, by decide⟩} : Finset (Fin 127))
  | 23 => ({⟨27, by decide⟩, ⟨97, by decide⟩} : Finset (Fin 127))
  | 24 => ({⟨24, by decide⟩, ⟨102, by decide⟩} : Finset (Fin 127))
  | 25 => ({⟨13, by decide⟩, ⟨18, by decide⟩, ⟨34, by decide⟩, ⟨47, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨61, by decide⟩, ⟨66, by decide⟩, ⟨73, by decide⟩, ⟨76, by decide⟩, ⟨86, by decide⟩, ⟨88, by decide⟩, ⟨93, by decide⟩, ⟨102, by decide⟩, ⟨104, by decide⟩, ⟨109, by decide⟩, ⟨114, by decide⟩, ⟨115, by decide⟩, ⟨121, by decide⟩, ⟨124, by decide⟩} : Finset (Fin 127))
  | 26 => ({⟨10, by decide⟩, ⟨16, by decide⟩, ⟨24, by decide⟩, ⟨34, by decide⟩, ⟨42, by decide⟩, ⟨49, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨70, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩, ⟨84, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨102, by decide⟩, ⟨107, by decide⟩, ⟨110, by decide⟩, ⟨116, by decide⟩, ⟨117, by decide⟩, ⟨124, by decide⟩} : Finset (Fin 127))
  | 27 => ({⟨12, by decide⟩, ⟨18, by decide⟩, ⟨24, by decide⟩, ⟨36, by decide⟩, ⟨46, by decide⟩, ⟨53, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨66, by decide⟩, ⟨72, by decide⟩, ⟨77, by decide⟩, ⟨86, by decide⟩, ⟨89, by decide⟩, ⟨92, by decide⟩, ⟨96, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩, ⟨113, by decide⟩, ⟨116, by decide⟩, ⟨126, by decide⟩} : Finset (Fin 127))
  | 28 => ({⟨0, by decide⟩, ⟨10, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨20, by decide⟩, ⟨26, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨36, by decide⟩, ⟨42, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨81, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨97, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨113, by decide⟩, ⟨114, by decide⟩, ⟨117, by decide⟩, ⟨118, by decide⟩, ⟨123, by decide⟩, ⟨124, by decide⟩} : Finset (Fin 127))
  | 29 => ({⟨0, by decide⟩, ⟨10, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨20, by decide⟩, ⟨26, by decide⟩, ⟨30, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨43, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨81, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨96, by decide⟩, ⟨100, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩, ⟨109, by decide⟩, ⟨110, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩, ⟨115, by decide⟩, ⟨116, by decide⟩, ⟨121, by decide⟩, ⟨122, by decide⟩, ⟨126, by decide⟩} : Finset (Fin 127))
  | 30 => ({⟨90, by decide⟩} : Finset (Fin 127))
  | 31 => ({⟨92, by decide⟩} : Finset (Fin 127))
  | 32 => ({⟨103, by decide⟩} : Finset (Fin 127))
  | 33 => ({⟨42, by decide⟩, ⟨46, by decide⟩, ⟨52, by decide⟩} : Finset (Fin 127))
  | 34 => ({⟨20, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩} : Finset (Fin 127))
  | 35 => ({⟨50, by decide⟩, ⟨100, by decide⟩, ⟨102, by decide⟩} : Finset (Fin 127))
  | 36 => ({⟨18, by decide⟩, ⟨54, by decide⟩, ⟨61, by decide⟩, ⟨70, by decide⟩, ⟨77, by decide⟩, ⟨92, by decide⟩, ⟨105, by decide⟩, ⟨111, by decide⟩} : Finset (Fin 127))
  | 37 => ({⟨14, by decide⟩, ⟨20, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨77, by decide⟩, ⟨90, by decide⟩, ⟨107, by decide⟩, ⟨117, by decide⟩} : Finset (Fin 127))
  | 38 => ({⟨27, by decide⟩, ⟨40, by decide⟩, ⟨46, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨80, by decide⟩, ⟨86, by decide⟩, ⟨97, by decide⟩} : Finset (Fin 127))
  | 39 => ({⟨12, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨27, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨88, by decide⟩, ⟨90, by decide⟩, ⟨96, by decide⟩, ⟨107, by decide⟩, ⟨109, by decide⟩, ⟨111, by decide⟩, ⟨113, by decide⟩, ⟨124, by decide⟩, ⟨126, by decide⟩} : Finset (Fin 127))
  | _ => ∅

private def extraMaskBlock486_02 (off : Nat) : Finset (Fin 127) :=
  match off with
  | 0 => ({⟨11, by decide⟩, ⟨13, by decide⟩, ⟨21, by decide⟩, ⟨43, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨65, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨87, by decide⟩, ⟨89, by decide⟩, ⟨97, by decide⟩, ⟨107, by decide⟩, ⟨109, by decide⟩, ⟨115, by decide⟩, ⟨117, by decide⟩, ⟨121, by decide⟩} : Finset (Fin 127))
  | 1 => ({⟨12, by decide⟩, ⟨32, by decide⟩, ⟨37, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨53, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨69, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨80, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨102, by decide⟩, ⟨105, by decide⟩, ⟨108, by decide⟩, ⟨111, by decide⟩, ⟨118, by decide⟩, ⟨121, by decide⟩, ⟨124, by decide⟩} : Finset (Fin 127))
  | 2 => ({⟨12, by decide⟩, ⟨18, by decide⟩, ⟨24, by decide⟩, ⟨34, by decide⟩, ⟨40, by decide⟩, ⟨47, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨76, by decide⟩, ⟨88, by decide⟩, ⟨93, by decide⟩, ⟨104, by decide⟩, ⟨109, by decide⟩, ⟨111, by decide⟩, ⟨118, by decide⟩, ⟨121, by decide⟩, ⟨124, by decide⟩} : Finset (Fin 127))
  | 3 => ({⟨12, by decide⟩, ⟨13, by decide⟩, ⟨24, by decide⟩, ⟨40, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨66, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨86, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨102, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨111, by decide⟩, ⟨114, by decide⟩, ⟨124, by decide⟩} : Finset (Fin 127))
  | 4 => ({⟨10, by decide⟩, ⟨11, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨24, by decide⟩, ⟨34, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨94, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨100, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩, ⟨111, by decide⟩, ⟨114, by decide⟩, ⟨115, by decide⟩, ⟨118, by decide⟩, ⟨122, by decide⟩, ⟨123, by decide⟩, ⟨126, by decide⟩} : Finset (Fin 127))
  | 5 => ({⟨0, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨18, by decide⟩, ⟨21, by decide⟩, ⟨26, by decide⟩, ⟨30, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨42, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩, ⟨84, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨96, by decide⟩, ⟨100, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨113, by decide⟩, ⟨114, by decide⟩, ⟨117, by decide⟩, ⟨118, by decide⟩, ⟨121, by decide⟩, ⟨122, by decide⟩, ⟨126, by decide⟩} : Finset (Fin 127))
  | 6 => ({⟨0, by decide⟩, ⟨68, by decide⟩} : Finset (Fin 127))
  | 7 => ({⟨110, by decide⟩} : Finset (Fin 127))
  | 8 => ({⟨56, by decide⟩, ⟨72, by decide⟩, ⟨92, by decide⟩, ⟨111, by decide⟩} : Finset (Fin 127))
  | 9 => ({⟨37, by decide⟩, ⟨97, by decide⟩} : Finset (Fin 127))
  | 10 => ({⟨50, by decide⟩, ⟨84, by decide⟩, ⟨86, by decide⟩} : Finset (Fin 127))
  | 11 => ({⟨12, by decide⟩, ⟨30, by decide⟩, ⟨52, by decide⟩, ⟨55, by decide⟩, ⟨75, by decide⟩, ⟨93, by decide⟩, ⟨106, by decide⟩, ⟨115, by decide⟩} : Finset (Fin 127))
  | 12 => ({⟨12, by decide⟩, ⟨24, by decide⟩, ⟨51, by decide⟩, ⟨56, by decide⟩, ⟨76, by decide⟩, ⟨88, by decide⟩, ⟨108, by decide⟩, ⟨115, by decide⟩} : Finset (Fin 127))
  | 13 => ({⟨11, by decide⟩, ⟨13, by decide⟩, ⟨20, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨46, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨81, by decide⟩, ⟨91, by decide⟩, ⟨93, by decide⟩, ⟨103, by decide⟩, ⟨105, by decide⟩, ⟨112, by decide⟩, ⟨114, by decide⟩, ⟨124, by decide⟩, ⟨126, by decide⟩} : Finset (Fin 127))
  | 14 => ({⟨12, by decide⟩, ⟨14, by decide⟩, ⟨30, by decide⟩, ⟨36, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨66, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨80, by decide⟩, ⟨91, by decide⟩, ⟨93, by decide⟩, ⟨104, by decide⟩, ⟨106, by decide⟩, ⟨115, by decide⟩, ⟨117, by decide⟩, ⟨122, by decide⟩} : Finset (Fin 127))
  | 15 => ({⟨12, by decide⟩, ⟨20, by decide⟩, ⟨30, by decide⟩, ⟨36, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨69, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨88, by decide⟩, ⟨93, by decide⟩, ⟨104, by decide⟩, ⟨109, by decide⟩, ⟨112, by decide⟩, ⟨117, by decide⟩, ⟨122, by decide⟩, ⟨123, by decide⟩} : Finset (Fin 127))
  | 16 => ({⟨10, by decide⟩, ⟨18, by decide⟩, ⟨26, by decide⟩, ⟨32, by decide⟩, ⟨40, by decide⟩, ⟨49, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨70, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩, ⟨86, by decide⟩, ⟨91, by decide⟩, ⟨94, by decide⟩, ⟨100, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩, ⟨116, by decide⟩, ⟨117, by decide⟩, ⟨124, by decide⟩} : Finset (Fin 127))
  | 17 => ({⟨10, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨16, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨42, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨86, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨91, by decide⟩, ⟨94, by decide⟩, ⟨100, by decide⟩, ⟨103, by decide⟩, ⟨106, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩, ⟨112, by decide⟩, ⟨113, by decide⟩, ⟨115, by decide⟩, ⟨118, by decide⟩, ⟨121, by decide⟩, ⟨123, by decide⟩, ⟨126, by decide⟩} : Finset (Fin 127))
  | 18 => ({⟨10, by decide⟩, ⟨11, by decide⟩, ⟨13, by decide⟩, ⟨20, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨46, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨86, by decide⟩, ⟨88, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨93, by decide⟩, ⟨96, by decide⟩, ⟨103, by decide⟩, ⟨105, by decide⟩, ⟨108, by decide⟩, ⟨110, by decide⟩, ⟨112, by decide⟩, ⟨114, by decide⟩, ⟨115, by decide⟩, ⟨117, by decide⟩, ⟨121, by decide⟩, ⟨124, by decide⟩, ⟨126, by decide⟩} : Finset (Fin 127))
  | 19 => ({⟨10, by decide⟩, ⟨49, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨86, by decide⟩, ⟨91, by decide⟩, ⟨94, by decide⟩, ⟨100, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩} : Finset (Fin 127))
  | 20 => ({⟨13, by decide⟩, ⟨37, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨77, by decide⟩, ⟨93, by decide⟩, ⟨103, by decide⟩, ⟨117, by decide⟩} : Finset (Fin 127))
  | 21 => ({⟨14, by decide⟩, ⟨16, by decide⟩, ⟨53, by decide⟩, ⟨56, by decide⟩, ⟨77, by decide⟩, ⟨94, by decide⟩, ⟨104, by decide⟩, ⟨118, by decide⟩} : Finset (Fin 127))
  | 22 => ({⟨14, by decide⟩, ⟨36, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨77, by decide⟩, ⟨91, by decide⟩, ⟨106, by decide⟩, ⟨117, by decide⟩} : Finset (Fin 127))
  | 23 => ({⟨26, by decide⟩, ⟨27, by decide⟩, ⟨40, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨86, by decide⟩, ⟨97, by decide⟩, ⟨100, by decide⟩} : Finset (Fin 127))
  | 24 => ({⟨0, by decide⟩, ⟨10, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩} : Finset (Fin 127))
  | 25 => ({⟨0, by decide⟩, ⟨10, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨84, by decide⟩, ⟨86, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨100, by decide⟩, ⟨102, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩, ⟨110, by decide⟩} : Finset (Fin 127))
  | 26 => ({⟨11, by decide⟩, ⟨21, by decide⟩, ⟨27, by decide⟩, ⟨37, by decide⟩, ⟨43, by decide⟩, ⟨47, by decide⟩, ⟨53, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨89, by decide⟩, ⟨91, by decide⟩, ⟨105, by decide⟩, ⟨107, by decide⟩, ⟨111, by decide⟩, ⟨117, by decide⟩, ⟨121, by decide⟩, ⟨123, by decide⟩} : Finset (Fin 127))
  | 27 => ({⟨11, by decide⟩, ⟨16, by decide⟩, ⟨26, by decide⟩, ⟨32, by decide⟩, ⟨42, by decide⟩, ⟨47, by decide⟩, ⟨53, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨70, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨89, by decide⟩, ⟨91, by decide⟩, ⟨105, by decide⟩, ⟨107, by decide⟩, ⟨112, by decide⟩, ⟨118, by decide⟩, ⟨122, by decide⟩, ⟨124, by decide⟩} : Finset (Fin 127))
  | 28 => ({⟨0, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨84, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨100, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩, ⟨115, by decide⟩, ⟨116, by decide⟩, ⟨117, by decide⟩, ⟨118, by decide⟩, ⟨121, by decide⟩, ⟨122, by decide⟩} : Finset (Fin 127))
  | 29 => ({⟨11, by decide⟩, ⟨14, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩, ⟨84, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨91, by decide⟩, ⟨94, by decide⟩, ⟨100, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨107, by decide⟩, ⟨110, by decide⟩, ⟨111, by decide⟩, ⟨114, by decide⟩, ⟨116, by decide⟩, ⟨117, by decide⟩, ⟨121, by decide⟩, ⟨123, by decide⟩, ⟨126, by decide⟩} : Finset (Fin 127))
  | 30 => ({⟨12, by decide⟩, ⟨13, by decide⟩, ⟨16, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩, ⟨86, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨102, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩, ⟨112, by decide⟩, ⟨113, by decide⟩, ⟨116, by decide⟩, ⟨117, by decide⟩, ⟨122, by decide⟩, ⟨123, by decide⟩, ⟨126, by decide⟩} : Finset (Fin 127))
  | 31 => ({⟨11, by decide⟩, ⟨13, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨78, by decide⟩, ⟨81, by decide⟩, ⟨87, by decide⟩, ⟨89, by decide⟩, ⟨91, by decide⟩, ⟨93, by decide⟩, ⟨97, by decide⟩, ⟨103, by decide⟩, ⟨105, by decide⟩, ⟨107, by decide⟩, ⟨109, by decide⟩, ⟨112, by decide⟩, ⟨114, by decide⟩, ⟨116, by decide⟩, ⟨118, by decide⟩, ⟨122, by decide⟩, ⟨124, by decide⟩, ⟨126, by decide⟩} : Finset (Fin 127))
  | 32 => ({⟨0, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨100, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩, ⟨113, by decide⟩, ⟨114, by decide⟩, ⟨123, by decide⟩, ⟨124, by decide⟩, ⟨126, by decide⟩} : Finset (Fin 127))
  | 33 => ({⟨0, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩, ⟨110, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩, ⟨113, by decide⟩, ⟨114, by decide⟩, ⟨123, by decide⟩, ⟨124, by decide⟩, ⟨126, by decide⟩} : Finset (Fin 127))
  | 34 => ({⟨37, by decide⟩, ⟨43, by decide⟩} : Finset (Fin 127))
  | 35 => ({⟨32, by decide⟩, ⟨100, by decide⟩} : Finset (Fin 127))
  | 36 => ({⟨53, by decide⟩, ⟨65, by decide⟩, ⟨115, by decide⟩} : Finset (Fin 127))
  | 37 => ({⟨11, by decide⟩, ⟨27, by decide⟩, ⟨51, by decide⟩, ⟨55, by decide⟩, ⟨75, by decide⟩, ⟨91, by decide⟩, ⟨103, by decide⟩, ⟨115, by decide⟩} : Finset (Fin 127))
  | 38 => ({⟨43, by decide⟩, ⟨51, by decide⟩, ⟨59, by decide⟩, ⟨71, by decide⟩, ⟨87, by decide⟩, ⟨107, by decide⟩, ⟨115, by decide⟩, ⟨123, by decide⟩} : Finset (Fin 127))
  | 39 => ({⟨46, by decide⟩, ⟨52, by decide⟩, ⟨60, by decide⟩, ⟨72, by decide⟩, ⟨90, by decide⟩, ⟨109, by decide⟩, ⟨115, by decide⟩, ⟨123, by decide⟩} : Finset (Fin 127))
  | _ => ∅

private def extraMaskBlock486_03 (off : Nat) : Finset (Fin 127) :=
  match off with
  | 0 => ({⟨10, by decide⟩, ⟨12, by decide⟩, ⟨16, by decide⟩, ⟨27, by decide⟩, ⟨40, by decide⟩, ⟨46, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨55, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩, ⟨72, by decide⟩, ⟨78, by decide⟩, ⟨84, by decide⟩, ⟨87, by decide⟩, ⟨93, by decide⟩, ⟨106, by decide⟩, ⟨108, by decide⟩, ⟨112, by decide⟩, ⟨118, by decide⟩, ⟨121, by decide⟩, ⟨123, by decide⟩} : Finset (Fin 127))
  | 1 => ({⟨11, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨24, by decide⟩, ⟨30, by decide⟩, ⟨54, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨84, by decide⟩, ⟨88, by decide⟩, ⟨94, by decide⟩, ⟨97, by decide⟩, ⟨103, by decide⟩, ⟨109, by decide⟩, ⟨112, by decide⟩, ⟨118, by decide⟩, ⟨122, by decide⟩, ⟨124, by decide⟩} : Finset (Fin 127))
  | 2 => ({⟨11, by decide⟩, ⟨14, by decide⟩, ⟨26, by decide⟩, ⟨42, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨84, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨100, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨112, by decide⟩, ⟨113, by decide⟩, ⟨124, by decide⟩} : Finset (Fin 127))
  | 3 => ({⟨0, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨47, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨80, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨96, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨109, by decide⟩, ⟨110, by decide⟩, ⟨113, by decide⟩, ⟨114, by decide⟩, ⟨115, by decide⟩, ⟨116, by decide⟩, ⟨121, by decide⟩, ⟨122, by decide⟩, ⟨123, by decide⟩, ⟨124, by decide⟩} : Finset (Fin 127))
  | 4 => ({⟨0, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨16, by decide⟩, ⟨21, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨40, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨96, by decide⟩, ⟨102, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩, ⟨117, by decide⟩, ⟨118, by decide⟩, ⟨121, by decide⟩, ⟨122, by decide⟩, ⟨123, by decide⟩, ⟨124, by decide⟩} : Finset (Fin 127))
  | 5 => (∅ : Finset (Fin 127))
  | 6 => ({⟨87, by decide⟩} : Finset (Fin 127))
  | 7 => ({⟨94, by decide⟩} : Finset (Fin 127))
  | 8 => ({⟨90, by decide⟩} : Finset (Fin 127))
  | 9 => ({⟨32, by decide⟩, ⟨42, by decide⟩} : Finset (Fin 127))
  | 10 => ({⟨40, by decide⟩, ⟨43, by decide⟩, ⟨51, by decide⟩} : Finset (Fin 127))
  | 11 => ({⟨21, by decide⟩, ⟨53, by decide⟩, ⟨61, by decide⟩, ⟨69, by decide⟩, ⟨77, by decide⟩, ⟨87, by decide⟩, ⟨109, by decide⟩, ⟨111, by decide⟩} : Finset (Fin 127))
  | 12 => ({⟨43, by decide⟩, ⟨81, by decide⟩} : Finset (Fin 127))
  | 13 => ({⟨30, by decide⟩, ⟨96, by decide⟩} : Finset (Fin 127))
  | 14 => ({⟨10, by decide⟩, ⟨13, by decide⟩, ⟨18, by decide⟩, ⟨21, by decide⟩, ⟨36, by decide⟩, ⟨42, by decide⟩, ⟨50, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨60, by decide⟩, ⟨65, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨75, by decide⟩, ⟨80, by decide⟩, ⟨89, by decide⟩, ⟨94, by decide⟩, ⟨97, by decide⟩, ⟨102, by decide⟩, ⟨104, by decide⟩, ⟨107, by decide⟩, ⟨112, by decide⟩, ⟨115, by decide⟩, ⟨121, by decide⟩, ⟨126, by decide⟩} : Finset (Fin 127))
  | 15 => ({⟨12, by decide⟩, ⟨14, by decide⟩, ⟨20, by decide⟩, ⟨46, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨66, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨88, by decide⟩, ⟨90, by decide⟩, ⟨96, by decide⟩, ⟨107, by decide⟩, ⟨109, by decide⟩, ⟨115, by decide⟩, ⟨117, by decide⟩, ⟨122, by decide⟩} : Finset (Fin 127))
  | 16 => ({⟨12, by decide⟩, ⟨14, by decide⟩, ⟨20, by decide⟩, ⟨36, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨69, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨80, by decide⟩, ⟨91, by decide⟩, ⟨93, by decide⟩, ⟨96, by decide⟩, ⟨107, by decide⟩, ⟨109, by decide⟩, ⟨115, by decide⟩, ⟨117, by decide⟩, ⟨122, by decide⟩} : Finset (Fin 127))
  | 17 => ({⟨12, by decide⟩, ⟨20, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩, ⟨62, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨90, by decide⟩, ⟨93, by decide⟩, ⟨96, by decide⟩, ⟨104, by decide⟩, ⟨107, by decide⟩, ⟨112, by decide⟩, ⟨115, by decide⟩, ⟨123, by decide⟩} : Finset (Fin 127))
  | 18 => ({⟨13, by decide⟩, ⟨21, by decide⟩, ⟨27, by decide⟩, ⟨34, by decide⟩, ⟨40, by decide⟩, ⟨52, by decide⟩, ⟨58, by decide⟩, ⟨62, by decide⟩, ⟨68, by decide⟩, ⟨74, by decide⟩, ⟨78, by decide⟩, ⟨86, by decide⟩, ⟨88, by decide⟩, ⟨92, by decide⟩, ⟨97, by decide⟩, ⟨103, by decide⟩, ⟨107, by decide⟩, ⟨111, by decide⟩, ⟨115, by decide⟩, ⟨121, by decide⟩} : Finset (Fin 127))
  | 19 => ({⟨0, by decide⟩, ⟨10, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨18, by decide⟩, ⟨21, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨43, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨80, by decide⟩, ⟨84, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨96, by decide⟩, ⟨100, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩, ⟨109, by decide⟩, ⟨110, by decide⟩, ⟨113, by decide⟩, ⟨114, by decide⟩, ⟨117, by decide⟩, ⟨118, by decide⟩, ⟨123, by decide⟩, ⟨124, by decide⟩} : Finset (Fin 127))
  | 20 => ({⟨0, by decide⟩, ⟨10, by decide⟩} : Finset (Fin 127))
  | 21 => ({⟨56, by decide⟩, ⟨72, by decide⟩, ⟨108, by decide⟩, ⟨111, by decide⟩} : Finset (Fin 127))
  | 22 => ({⟨55, by decide⟩, ⟨72, by decide⟩, ⟨106, by decide⟩, ⟨112, by decide⟩} : Finset (Fin 127))
  | 23 => ({⟨16, by decide⟩, ⟨26, by decide⟩} : Finset (Fin 127))
  | 24 => ({⟨49, by decide⟩, ⟨57, by decide⟩, ⟨66, by decide⟩, ⟨74, by decide⟩, ⟨90, by decide⟩, ⟨96, by decide⟩, ⟨104, by decide⟩, ⟨112, by decide⟩} : Finset (Fin 127))
  | 25 => ({⟨12, by decide⟩, ⟨14, by decide⟩, ⟨20, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨50, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩} : Finset (Fin 127))
  | 26 => ({⟨10, by decide⟩, ⟨12, by decide⟩, ⟨21, by decide⟩, ⟨26, by decide⟩, ⟨40, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨56, by decide⟩, ⟨62, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩, ⟨77, by decide⟩, ⟨84, by decide⟩, ⟨87, by decide⟩, ⟨93, by decide⟩, ⟨96, by decide⟩, ⟨102, by decide⟩, ⟨105, by decide⟩, ⟨107, by decide⟩, ⟨112, by decide⟩, ⟨118, by decide⟩, ⟨121, by decide⟩, ⟨123, by decide⟩} : Finset (Fin 127))
  | 27 => ({⟨10, by decide⟩, ⟨12, by decide⟩, ⟨16, by decide⟩, ⟨27, by decide⟩, ⟨40, by decide⟩, ⟨46, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨55, by decide⟩, ⟨61, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩, ⟨77, by decide⟩, ⟨81, by decide⟩, ⟨88, by decide⟩, ⟨94, by decide⟩, ⟨96, by decide⟩, ⟨102, by decide⟩, ⟨105, by decide⟩, ⟨107, by decide⟩, ⟨111, by decide⟩, ⟨117, by decide⟩, ⟨122, by decide⟩, ⟨124, by decide⟩} : Finset (Fin 127))
  | 28 => ({⟨10, by decide⟩, ⟨13, by decide⟩, ⟨18, by decide⟩, ⟨21, by decide⟩, ⟨32, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨76, by decide⟩, ⟨84, by decide⟩, ⟨90, by decide⟩, ⟨93, by decide⟩, ⟨97, by decide⟩, ⟨102, by decide⟩, ⟨104, by decide⟩, ⟨107, by decide⟩, ⟨112, by decide⟩, ⟨115, by decide⟩, ⟨121, by decide⟩, ⟨126, by decide⟩} : Finset (Fin 127))
  | 29 => ({⟨12, by decide⟩, ⟨20, by decide⟩, ⟨30, by decide⟩, ⟨34, by decide⟩, ⟨40, by decide⟩, ⟨53, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨66, by decide⟩, ⟨72, by decide⟩, ⟨77, by decide⟩, ⟨80, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨102, by decide⟩, ⟨105, by decide⟩, ⟨108, by decide⟩, ⟨113, by decide⟩, ⟨116, by decide⟩, ⟨126, by decide⟩} : Finset (Fin 127))
  | 30 => ({⟨10, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨26, by decide⟩, ⟨32, by decide⟩, ⟨40, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨84, by decide⟩, ⟨87, by decide⟩, ⟨90, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨102, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨107, by decide⟩, ⟨110, by decide⟩, ⟨112, by decide⟩, ⟨113, by decide⟩, ⟨115, by decide⟩, ⟨118, by decide⟩, ⟨121, by decide⟩, ⟨123, by decide⟩, ⟨126, by decide⟩} : Finset (Fin 127))
  | 31 => ({⟨10, by decide⟩, ⟨11, by decide⟩, ⟨13, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨21, by decide⟩, ⟨30, by decide⟩, ⟨36, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨80, by decide⟩, ⟨87, by decide⟩, ⟨89, by decide⟩, ⟨92, by decide⟩, ⟨94, by decide⟩, ⟨97, by decide⟩, ⟨100, by decide⟩, ⟨102, by decide⟩, ⟨104, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩, ⟨109, by decide⟩, ⟨112, by decide⟩, ⟨114, by decide⟩, ⟨115, by decide⟩, ⟨117, by decide⟩, ⟨121, by decide⟩, ⟨124, by decide⟩, ⟨126, by decide⟩} : Finset (Fin 127))
  | 32 => ({⟨10, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨27, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨46, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨81, by decide⟩, ⟨88, by decide⟩, ⟨90, by decide⟩, ⟨92, by decide⟩, ⟨94, by decide⟩, ⟨96, by decide⟩, ⟨100, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨105, by decide⟩, ⟨107, by decide⟩, ⟨109, by decide⟩, ⟨111, by decide⟩, ⟨113, by decide⟩, ⟨115, by decide⟩, ⟨117, by decide⟩, ⟨122, by decide⟩, ⟨124, by decide⟩, ⟨126, by decide⟩} : Finset (Fin 127))
  | 33 => ({⟨0, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨16, by decide⟩, ⟨20, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩, ⟨32, by decide⟩, ⟨36, by decide⟩, ⟨40, by decide⟩, ⟨43, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨81, by decide⟩, ⟨86, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨97, by decide⟩, ⟨102, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩, ⟨109, by decide⟩, ⟨110, by decide⟩, ⟨113, by decide⟩, ⟨114, by decide⟩, ⟨117, by decide⟩, ⟨118, by decide⟩, ⟨121, by decide⟩, ⟨122, by decide⟩, ⟨126, by decide⟩} : Finset (Fin 127))
  | 34 => ({⟨110, by decide⟩} : Finset (Fin 127))
  | 35 => ({⟨108, by decide⟩} : Finset (Fin 127))
  | 36 => ({⟨16, by decide⟩, ⟨26, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨51, by decide⟩, ⟨54, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩} : Finset (Fin 127))
  | 37 => ({⟨37, by decide⟩, ⟨53, by decide⟩, ⟨61, by decide⟩, ⟨69, by decide⟩, ⟨77, by decide⟩, ⟨93, by decide⟩, ⟨103, by decide⟩, ⟨111, by decide⟩} : Finset (Fin 127))
  | 38 => ({⟨16, by decide⟩, ⟨53, by decide⟩, ⟨62, by decide⟩, ⟨70, by decide⟩, ⟨77, by decide⟩, ⟨94, by decide⟩, ⟨104, by decide⟩, ⟨112, by decide⟩} : Finset (Fin 127))
  | 39 => ({⟨50, by decide⟩, ⟨57, by decide⟩, ⟨66, by decide⟩, ⟨73, by decide⟩, ⟨86, by decide⟩, ⟨93, by decide⟩, ⟨108, by decide⟩, ⟨111, by decide⟩} : Finset (Fin 127))
  | _ => ∅

private def extraMaskBlock486_04 (off : Nat) : Finset (Fin 127) :=
  match off with
  | 0 => ({⟨40, by decide⟩, ⟨86, by decide⟩} : Finset (Fin 127))
  | 1 => ({⟨0, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩, ⟨40, by decide⟩, ⟨43, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨68, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩, ⟨115, by decide⟩, ⟨116, by decide⟩} : Finset (Fin 127))
  | 2 => ({⟨0, by decide⟩, ⟨26, by decide⟩, ⟨30, by decide⟩, ⟨42, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨68, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩, ⟨109, by decide⟩, ⟨110, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩, ⟨115, by decide⟩, ⟨116, by decide⟩} : Finset (Fin 127))
  | 3 => ({⟨0, by decide⟩, ⟨24, by decide⟩, ⟨30, by decide⟩, ⟨40, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨113, by decide⟩, ⟨114, by decide⟩, ⟨115, by decide⟩, ⟨116, by decide⟩} : Finset (Fin 127))
  | 4 => ({⟨11, by decide⟩, ⟨13, by decide⟩, ⟨21, by decide⟩, ⟨37, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨81, by decide⟩, ⟨91, by decide⟩, ⟨93, by decide⟩, ⟨97, by decide⟩, ⟨107, by decide⟩, ⟨109, by decide⟩, ⟨115, by decide⟩, ⟨117, by decide⟩, ⟨121, by decide⟩} : Finset (Fin 127))
  | 5 => ({⟨11, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨32, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨84, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨100, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨115, by decide⟩, ⟨118, by decide⟩, ⟨122, by decide⟩} : Finset (Fin 127))
  | 6 => ({⟨13, by decide⟩, ⟨21, by decide⟩, ⟨37, by decide⟩, ⟨47, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨81, by decide⟩, ⟨89, by decide⟩, ⟨91, by decide⟩, ⟨97, by decide⟩, ⟨105, by decide⟩, ⟨107, by decide⟩, ⟨113, by decide⟩, ⟨115, by decide⟩, ⟨121, by decide⟩, ⟨123, by decide⟩} : Finset (Fin 127))
  | 7 => ({⟨14, by decide⟩, ⟨16, by decide⟩, ⟨32, by decide⟩, ⟨47, by decide⟩, ⟨53, by decide⟩, ⟨56, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨84, by decide⟩, ⟨89, by decide⟩, ⟨91, by decide⟩, ⟨100, by decide⟩, ⟨105, by decide⟩, ⟨107, by decide⟩, ⟨113, by decide⟩, ⟨115, by decide⟩, ⟨122, by decide⟩, ⟨124, by decide⟩} : Finset (Fin 127))
  | 8 => ({⟨0, by decide⟩, ⟨10, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨18, by decide⟩, ⟨21, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩, ⟨32, by decide⟩, ⟨36, by decide⟩, ⟨42, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨80, by decide⟩, ⟨84, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨97, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩, ⟨115, by decide⟩, ⟨116, by decide⟩, ⟨121, by decide⟩, ⟨122, by decide⟩, ⟨126, by decide⟩} : Finset (Fin 127))
  | _ => ∅

def extraMaskBridge486 : Fin 169 → Finset (Fin 127) := fun i =>
  match i.val / 40 with
  | 0 => extraMaskBlock486_00 (i.val % 40)
  | 1 => extraMaskBlock486_01 (i.val % 40)
  | 2 => extraMaskBlock486_02 (i.val % 40)
  | 3 => extraMaskBlock486_03 (i.val % 40)
  | 4 => extraMaskBlock486_04 (i.val % 40)
  | _ => ∅

def deadMaskBridge486 : Finset (Fin 127) := Finset.univ.image deadEmb486

def liveRowBridge486 (i : Fin 169) (X : Fin 127 → Int) : Int :=
  ∑ j : Fin 40, occCoeff_486 i j * X (livePoint486 j)

def fullRowBridge486 (i : Fin 169) (X : Fin 127 → Int) : Int :=
  liveRowBridge486 i X + evalSet127_486 (extraMaskBridge486 i) X

def fullTotalBridge486 (X : Fin 127 → Int) : Int :=
  (∑ j : Fin 40, X (livePoint486 j)) + evalSet127_486 deadMaskBridge486 X

structure FullBridge486Alg (X : Fin 127 → Int) : Prop where
  hOcc : ∀ i : Fin 169, fullRowBridge486 i X ≤ occRhs_486 i
  hDeadCap : ∀ d : Fin 87, X (deadPoint486 d) ≤ 0
  hTotal : (18 : Int) ≤ fullTotalBridge486 X
  hNonneg : ∀ q : Fin 127, 0 ≤ X q

lemma evalSet127_486_nonneg (s : Finset (Fin 127)) (X : Fin 127 → Int) (hX : ∀ q, 0 ≤ X q) :
    0 ≤ evalSet127_486 s X := by
  unfold evalSet127_486
  exact Finset.sum_nonneg (by intro q _; exact hX q)

lemma red_row_of_full_bridge486_alg (X : Fin 127 → Int) (h : FullBridge486Alg X) (i : Fin 169) :
    (∑ j : Fin 40, occCoeff_486 i j * X (livePoint486 j)) ≤ occRhs_486 i := by
  have hfull := h.hOcc i
  have hextra : 0 ≤ evalSet127_486 (extraMaskBridge486 i) X := evalSet127_486_nonneg _ X h.hNonneg
  change liveRowBridge486 i X ≤ occRhs_486 i
  unfold fullRowBridge486 at hfull
  omega

theorem deadPointBridge486_zero_alg (X : Fin 127 → Int) (h : FullBridge486Alg X) :
    ∀ d : Fin 87, X (deadPoint486 d) = 0 := by
  intro d
  have hn := h.hNonneg (deadPoint486 d)
  have hc := h.hDeadCap d
  omega

lemma evalSet127_deadMaskBridge486_zero_alg (X : Fin 127 → Int) (h : FullBridge486Alg X) :
    evalSet127_486 deadMaskBridge486 X = 0 := by
  have hz := deadPointBridge486_zero_alg X h
  unfold deadMaskBridge486 evalSet127_486
  rw [Finset.sum_image]
  · simp [deadEmb486, hz]
  · intro a _ b _ hab
    exact deadEmb486.injective hab

theorem orbit486_reduced_root_of_full_bridge_alg
    (X : Fin 127 → Int) (h : FullBridge486Alg X) :
    S_486.RootHolds (fun j : Fin 40 => X (livePoint486 j)) := by
  constructor
  · intro i
    exact red_row_of_full_bridge486_alg X h i
  · have ht := h.hTotal
    have hdz := evalSet127_deadMaskBridge486_zero_alg X h
    simp [fullTotalBridge486, hdz] at ht ⊢
    exact ht
  · intro j
    exact h.hNonneg (livePoint486 j)

theorem orbit486_no_full_bridge_model_alg (X : Fin 127 → Int) (h : FullBridge486Alg X) : False := by
  exact orbit486_no_model (fun j : Fin 40 => X (livePoint486 j)) (orbit486_reduced_root_of_full_bridge_alg X h)

end QiushiMatmul
