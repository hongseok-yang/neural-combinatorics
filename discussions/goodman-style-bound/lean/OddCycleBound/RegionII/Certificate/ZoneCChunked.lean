import OddCycleBound.RegionII.Certificate.ZoneCChunks.Chunk00
import OddCycleBound.RegionII.Certificate.ZoneCChunks.Chunk01
import OddCycleBound.RegionII.Certificate.ZoneCChunks.Chunk02
import OddCycleBound.RegionII.Certificate.ZoneCChunks.Chunk03
import OddCycleBound.RegionII.Certificate.ZoneCChunks.Chunk04
import OddCycleBound.RegionII.Certificate.ZoneCChunks.Chunk05
import OddCycleBound.RegionII.Certificate.ZoneCChunks.Chunk06
import OddCycleBound.RegionII.Certificate.ZoneCChunks.Chunk07
import OddCycleBound.RegionII.Certificate.ZoneCChunks.Chunk08
import OddCycleBound.RegionII.Certificate.ZoneCChunks.Chunk09
import OddCycleBound.RegionII.Certificate.ZoneCChunks.Chunk10
import OddCycleBound.RegionII.Certificate.ZoneCChunks.Chunk11
import OddCycleBound.RegionII.Certificate.ZoneCChunks.Chunk12
import OddCycleBound.RegionII.Certificate.ZoneCChunks.Chunk13
import OddCycleBound.RegionII.Certificate.ZoneCChunks.Chunk14
import OddCycleBound.RegionII.Certificate.ZoneCChunks.Chunk15
import OddCycleBound.RegionII.Certificate.ZoneCChunks.Chunk16
import OddCycleBound.RegionII.Certificate.ZoneCChunks.Chunk17
import OddCycleBound.RegionII.Certificate.ZoneCChunks.Chunk18
import OddCycleBound.RegionII.Certificate.ZoneCChunks.Chunk19
import OddCycleBound.RegionII.Certificate.ZoneCChunks.Chunk20
import OddCycleBound.RegionII.Certificate.ZoneCChunks.Chunk21

/-! Deterministically generated bounded assembly of the Zone-C tree. -/

namespace OddCycleBound.RegionII.Certificate

def zoneCAssembly000 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1
    zoneCChunk001 zoneCChunk002

theorem zoneCAssembly000_valid :
    zoneCAssembly000.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1 = true := by
  unfold zoneCAssembly000
  exact BoxTree.validC_splitK zoneCChunk001_valid zoneCChunk002_valid

def zoneCAssembly001 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1
    zoneCAssembly000 zoneCChunk003

theorem zoneCAssembly001_valid :
    zoneCAssembly001.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1 = true := by
  unfold zoneCAssembly001
  exact BoxTree.validC_splitE zoneCAssembly000_valid zoneCChunk003_valid

def zoneCAssembly002 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1)).1
    zoneCChunk004 zoneCChunk005

theorem zoneCAssembly002_valid :
    zoneCAssembly002.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1)).1 = true := by
  unfold zoneCAssembly002
  exact BoxTree.validC_splitK zoneCChunk004_valid zoneCChunk005_valid

def zoneCAssembly003 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1
    zoneCAssembly002 zoneCChunk006

theorem zoneCAssembly003_valid :
    zoneCAssembly003.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1 = true := by
  unfold zoneCAssembly003
  exact BoxTree.validC_splitE zoneCAssembly002_valid zoneCChunk006_valid

def zoneCAssembly004 : BoxTree :=
  .splitE (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1
    zoneCChunk007 zoneCChunk008

theorem zoneCAssembly004_valid :
    zoneCAssembly004.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1 = true := by
  unfold zoneCAssembly004
  exact BoxTree.validC_splitE zoneCChunk007_valid zoneCChunk008_valid

def zoneCAssembly005 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2
    zoneCAssembly004 zoneCChunk009

theorem zoneCAssembly005_valid :
    zoneCAssembly005.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly005
  exact BoxTree.validC_splitE zoneCAssembly004_valid zoneCChunk009_valid

def zoneCAssembly006 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1
    zoneCAssembly003 zoneCAssembly005

theorem zoneCAssembly006_valid :
    zoneCAssembly006.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1 = true := by
  unfold zoneCAssembly006
  exact BoxTree.validC_splitK zoneCAssembly003_valid zoneCAssembly005_valid

def zoneCAssembly007 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2
    zoneCAssembly006 zoneCChunk010

theorem zoneCAssembly007_valid :
    zoneCAssembly007.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly007
  exact BoxTree.validC_splitE zoneCAssembly006_valid zoneCChunk010_valid

def zoneCAssembly008 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1
    zoneCAssembly001 zoneCAssembly007

theorem zoneCAssembly008_valid :
    zoneCAssembly008.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1 = true := by
  unfold zoneCAssembly008
  exact BoxTree.validC_splitK zoneCAssembly001_valid zoneCAssembly007_valid

def zoneCAssembly009 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2
    zoneCAssembly008 zoneCChunk011

theorem zoneCAssembly009_valid :
    zoneCAssembly009.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2 = true := by
  unfold zoneCAssembly009
  exact BoxTree.validC_splitE zoneCAssembly008_valid zoneCChunk011_valid

def zoneCAssembly010 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1
    zoneCChunk000 zoneCAssembly009

theorem zoneCAssembly010_valid :
    zoneCAssembly010.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly010
  exact BoxTree.validC_splitK zoneCChunk000_valid zoneCAssembly009_valid

def zoneCAssembly011 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).1)).1
    zoneCChunk012 zoneCChunk013

theorem zoneCAssembly011_valid :
    zoneCAssembly011.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly011
  exact BoxTree.validC_splitE zoneCChunk012_valid zoneCChunk013_valid

def zoneCAssembly012 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).1)).2
    zoneCChunk014 zoneCChunk015

theorem zoneCAssembly012_valid :
    zoneCAssembly012.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).1)).2 = true := by
  unfold zoneCAssembly012
  exact BoxTree.validC_splitE zoneCChunk014_valid zoneCChunk015_valid

def zoneCAssembly013 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).1
    zoneCAssembly011 zoneCAssembly012

theorem zoneCAssembly013_valid :
    zoneCAssembly013.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly013
  exact BoxTree.validC_splitK zoneCAssembly011_valid zoneCAssembly012_valid

def zoneCAssembly014 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).2
    zoneCChunk016 zoneCChunk017

theorem zoneCAssembly014_valid :
    zoneCAssembly014.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).2 = true := by
  unfold zoneCAssembly014
  exact BoxTree.validC_splitK zoneCChunk016_valid zoneCChunk017_valid

def zoneCAssembly015 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1
    zoneCAssembly013 zoneCAssembly014

theorem zoneCAssembly015_valid :
    zoneCAssembly015.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly015
  exact BoxTree.validC_splitE zoneCAssembly013_valid zoneCAssembly014_valid

def zoneCAssembly016 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).2)).1)).1)).1
    zoneCChunk018 zoneCChunk019

theorem zoneCAssembly016_valid :
    zoneCAssembly016.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).2)).1)).1)).1 = true := by
  unfold zoneCAssembly016
  exact BoxTree.validC_splitK zoneCChunk018_valid zoneCChunk019_valid

def zoneCAssembly017 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).2)).1)).1
    zoneCAssembly016 zoneCChunk020

theorem zoneCAssembly017_valid :
    zoneCAssembly017.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).2)).1)).1 = true := by
  unfold zoneCAssembly017
  exact BoxTree.validC_splitE zoneCAssembly016_valid zoneCChunk020_valid

def zoneCAssembly018 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).2)).1)).2)).1)).1
    zoneCChunk021 zoneCChunk022

theorem zoneCAssembly018_valid :
    zoneCAssembly018.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).2)).1)).2)).1)).1 = true := by
  unfold zoneCAssembly018
  exact BoxTree.validC_splitE zoneCChunk021_valid zoneCChunk022_valid

def zoneCAssembly019 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).2)).1)).2)).1)).2
    zoneCChunk023 zoneCChunk024

theorem zoneCAssembly019_valid :
    zoneCAssembly019.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).2)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly019
  exact BoxTree.validC_splitE zoneCChunk023_valid zoneCChunk024_valid

def zoneCAssembly020 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).2)).1)).2)).1
    zoneCAssembly018 zoneCAssembly019

theorem zoneCAssembly020_valid :
    zoneCAssembly020.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).2)).1)).2)).1 = true := by
  unfold zoneCAssembly020
  exact BoxTree.validC_splitK zoneCAssembly018_valid zoneCAssembly019_valid

def zoneCAssembly021 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).2)).1)).2
    zoneCAssembly020 zoneCChunk025

theorem zoneCAssembly021_valid :
    zoneCAssembly021.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly021
  exact BoxTree.validC_splitE zoneCAssembly020_valid zoneCChunk025_valid

def zoneCAssembly022 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).2)).1
    zoneCAssembly017 zoneCAssembly021

theorem zoneCAssembly022_valid :
    zoneCAssembly022.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).2)).1 = true := by
  unfold zoneCAssembly022
  exact BoxTree.validC_splitK zoneCAssembly017_valid zoneCAssembly021_valid

def zoneCAssembly023 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).2)).2)).1
    zoneCChunk026 zoneCChunk027

theorem zoneCAssembly023_valid :
    zoneCAssembly023.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).2)).2)).1 = true := by
  unfold zoneCAssembly023
  exact BoxTree.validC_splitE zoneCChunk026_valid zoneCChunk027_valid

def zoneCAssembly024 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).2)).2)).2
    zoneCChunk028 zoneCChunk029

theorem zoneCAssembly024_valid :
    zoneCAssembly024.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).2)).2)).2 = true := by
  unfold zoneCAssembly024
  exact BoxTree.validC_splitE zoneCChunk028_valid zoneCChunk029_valid

def zoneCAssembly025 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).2)).2
    zoneCAssembly023 zoneCAssembly024

theorem zoneCAssembly025_valid :
    zoneCAssembly025.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).2)).2 = true := by
  unfold zoneCAssembly025
  exact BoxTree.validC_splitK zoneCAssembly023_valid zoneCAssembly024_valid

def zoneCAssembly026 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).2
    zoneCAssembly022 zoneCAssembly025

theorem zoneCAssembly026_valid :
    zoneCAssembly026.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).2 = true := by
  unfold zoneCAssembly026
  exact BoxTree.validC_splitE zoneCAssembly022_valid zoneCAssembly025_valid

def zoneCAssembly027 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1
    zoneCAssembly015 zoneCAssembly026

theorem zoneCAssembly027_valid :
    zoneCAssembly027.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1 = true := by
  unfold zoneCAssembly027
  exact BoxTree.validC_splitK zoneCAssembly015_valid zoneCAssembly026_valid

def zoneCAssembly028 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).1
    zoneCChunk030 zoneCChunk031

theorem zoneCAssembly028_valid :
    zoneCAssembly028.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).1 = true := by
  unfold zoneCAssembly028
  exact BoxTree.validC_splitK zoneCChunk030_valid zoneCChunk031_valid

def zoneCAssembly029 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).2
    zoneCChunk032 zoneCChunk033

theorem zoneCAssembly029_valid :
    zoneCAssembly029.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).2 = true := by
  unfold zoneCAssembly029
  exact BoxTree.validC_splitE zoneCChunk032_valid zoneCChunk033_valid

def zoneCAssembly030 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2
    zoneCAssembly028 zoneCAssembly029

theorem zoneCAssembly030_valid :
    zoneCAssembly030.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2 = true := by
  unfold zoneCAssembly030
  exact BoxTree.validC_splitK zoneCAssembly028_valid zoneCAssembly029_valid

def zoneCAssembly031 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1
    zoneCAssembly027 zoneCAssembly030

theorem zoneCAssembly031_valid :
    zoneCAssembly031.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1 = true := by
  unfold zoneCAssembly031
  exact BoxTree.validC_splitE zoneCAssembly027_valid zoneCAssembly030_valid

def zoneCAssembly032 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1)).1)).1)).1)).1
    zoneCChunk034 zoneCChunk035

theorem zoneCAssembly032_valid :
    zoneCAssembly032.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly032
  exact BoxTree.validC_splitE zoneCChunk034_valid zoneCChunk035_valid

def zoneCAssembly033 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1)).1)).1)).1)).2
    zoneCChunk036 zoneCChunk037

theorem zoneCAssembly033_valid :
    zoneCAssembly033.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1)).1)).1)).1)).2 = true := by
  unfold zoneCAssembly033
  exact BoxTree.validC_splitE zoneCChunk036_valid zoneCChunk037_valid

def zoneCAssembly034 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1)).1)).1)).1
    zoneCAssembly032 zoneCAssembly033

theorem zoneCAssembly034_valid :
    zoneCAssembly034.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly034
  exact BoxTree.validC_splitK zoneCAssembly032_valid zoneCAssembly033_valid

def zoneCAssembly035 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1)).1)).1
    zoneCAssembly034 zoneCChunk038

theorem zoneCAssembly035_valid :
    zoneCAssembly035.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly035
  exact BoxTree.validC_splitE zoneCAssembly034_valid zoneCChunk038_valid

def zoneCAssembly036 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1)).1)).2)).1)).1
    zoneCChunk039 zoneCChunk040

theorem zoneCAssembly036_valid :
    zoneCAssembly036.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1)).1)).2)).1)).1 = true := by
  unfold zoneCAssembly036
  exact BoxTree.validC_splitE zoneCChunk039_valid zoneCChunk040_valid

def zoneCAssembly037 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1)).1)).2)).1)).2
    zoneCChunk041 zoneCChunk042

theorem zoneCAssembly037_valid :
    zoneCAssembly037.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly037
  exact BoxTree.validC_splitE zoneCChunk041_valid zoneCChunk042_valid

def zoneCAssembly038 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1)).1)).2)).1
    zoneCAssembly036 zoneCAssembly037

theorem zoneCAssembly038_valid :
    zoneCAssembly038.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1)).1)).2)).1 = true := by
  unfold zoneCAssembly038
  exact BoxTree.validC_splitK zoneCAssembly036_valid zoneCAssembly037_valid

def zoneCAssembly039 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1)).1)).2
    zoneCAssembly038 zoneCChunk043

theorem zoneCAssembly039_valid :
    zoneCAssembly039.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1)).1)).2 = true := by
  unfold zoneCAssembly039
  exact BoxTree.validC_splitE zoneCAssembly038_valid zoneCChunk043_valid

def zoneCAssembly040 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1)).1
    zoneCAssembly035 zoneCAssembly039

theorem zoneCAssembly040_valid :
    zoneCAssembly040.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1)).1 = true := by
  unfold zoneCAssembly040
  exact BoxTree.validC_splitK zoneCAssembly035_valid zoneCAssembly039_valid

def zoneCAssembly041 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1)).2)).1
    zoneCChunk044 zoneCChunk045

theorem zoneCAssembly041_valid :
    zoneCAssembly041.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1)).2)).1 = true := by
  unfold zoneCAssembly041
  exact BoxTree.validC_splitE zoneCChunk044_valid zoneCChunk045_valid

def zoneCAssembly042 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1)).2)).2
    zoneCChunk046 zoneCChunk047

theorem zoneCAssembly042_valid :
    zoneCAssembly042.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1)).2)).2 = true := by
  unfold zoneCAssembly042
  exact BoxTree.validC_splitE zoneCChunk046_valid zoneCChunk047_valid

def zoneCAssembly043 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1)).2
    zoneCAssembly041 zoneCAssembly042

theorem zoneCAssembly043_valid :
    zoneCAssembly043.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1)).2 = true := by
  unfold zoneCAssembly043
  exact BoxTree.validC_splitK zoneCAssembly041_valid zoneCAssembly042_valid

def zoneCAssembly044 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1
    zoneCAssembly040 zoneCAssembly043

theorem zoneCAssembly044_valid :
    zoneCAssembly044.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).1 = true := by
  unfold zoneCAssembly044
  exact BoxTree.validC_splitE zoneCAssembly040_valid zoneCAssembly043_valid

def zoneCAssembly045 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).1)).1)).2
    zoneCChunk049 zoneCChunk050

theorem zoneCAssembly045_valid :
    zoneCAssembly045.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).1)).1)).2 = true := by
  unfold zoneCAssembly045
  exact BoxTree.validC_splitK zoneCChunk049_valid zoneCChunk050_valid

def zoneCAssembly046 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).1)).1
    zoneCChunk048 zoneCAssembly045

theorem zoneCAssembly046_valid :
    zoneCAssembly046.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).1)).1 = true := by
  unfold zoneCAssembly046
  exact BoxTree.validC_splitE zoneCChunk048_valid zoneCAssembly045_valid

def zoneCAssembly047 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).1)).2
    zoneCChunk051 zoneCChunk052

theorem zoneCAssembly047_valid :
    zoneCAssembly047.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).1)).2 = true := by
  unfold zoneCAssembly047
  exact BoxTree.validC_splitE zoneCChunk051_valid zoneCChunk052_valid

def zoneCAssembly048 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).1
    zoneCAssembly046 zoneCAssembly047

theorem zoneCAssembly048_valid :
    zoneCAssembly048.validC (RatBox.splitE ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).1 = true := by
  unfold zoneCAssembly048
  exact BoxTree.validC_splitK zoneCAssembly046_valid zoneCAssembly047_valid

def zoneCAssembly049 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).2
    zoneCChunk054 zoneCChunk055

theorem zoneCAssembly049_valid :
    zoneCAssembly049.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).2 = true := by
  unfold zoneCAssembly049
  exact BoxTree.validC_splitE zoneCChunk054_valid zoneCChunk055_valid

def zoneCAssembly050 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2
    zoneCChunk053 zoneCAssembly049

theorem zoneCAssembly050_valid :
    zoneCAssembly050.validC (RatBox.splitE ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly050
  exact BoxTree.validC_splitK zoneCChunk053_valid zoneCAssembly049_valid

def zoneCAssembly051 : BoxTree :=
  .splitE (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1
    zoneCAssembly048 zoneCAssembly050

theorem zoneCAssembly051_valid :
    zoneCAssembly051.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1 = true := by
  unfold zoneCAssembly051
  exact BoxTree.validC_splitE zoneCAssembly048_valid zoneCAssembly050_valid

def zoneCAssembly052 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).1
    zoneCChunk056 zoneCChunk057

theorem zoneCAssembly052_valid :
    zoneCAssembly052.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).1 = true := by
  unfold zoneCAssembly052
  exact BoxTree.validC_splitE zoneCChunk056_valid zoneCChunk057_valid

def zoneCAssembly053 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2
    zoneCChunk058 zoneCChunk059

theorem zoneCAssembly053_valid :
    zoneCAssembly053.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2 = true := by
  unfold zoneCAssembly053
  exact BoxTree.validC_splitE zoneCChunk058_valid zoneCChunk059_valid

def zoneCAssembly054 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2
    zoneCAssembly052 zoneCAssembly053

theorem zoneCAssembly054_valid :
    zoneCAssembly054.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2 = true := by
  unfold zoneCAssembly054
  exact BoxTree.validC_splitK zoneCAssembly052_valid zoneCAssembly053_valid

def zoneCAssembly055 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2
    zoneCAssembly051 zoneCAssembly054

theorem zoneCAssembly055_valid :
    zoneCAssembly055.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly055
  exact BoxTree.validC_splitE zoneCAssembly051_valid zoneCAssembly054_valid

def zoneCAssembly056 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1
    zoneCAssembly044 zoneCAssembly055

theorem zoneCAssembly056_valid :
    zoneCAssembly056.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1 = true := by
  unfold zoneCAssembly056
  exact BoxTree.validC_splitK zoneCAssembly044_valid zoneCAssembly055_valid

def zoneCAssembly057 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).1)).1
    zoneCChunk060 zoneCChunk061

theorem zoneCAssembly057_valid :
    zoneCAssembly057.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).1)).1 = true := by
  unfold zoneCAssembly057
  exact BoxTree.validC_splitK zoneCChunk060_valid zoneCChunk061_valid

def zoneCAssembly058 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).1
    zoneCAssembly057 zoneCChunk062

theorem zoneCAssembly058_valid :
    zoneCAssembly058.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).1 = true := by
  unfold zoneCAssembly058
  exact BoxTree.validC_splitE zoneCAssembly057_valid zoneCChunk062_valid

def zoneCAssembly059 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).1
    zoneCChunk063 zoneCChunk064

theorem zoneCAssembly059_valid :
    zoneCAssembly059.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).1 = true := by
  unfold zoneCAssembly059
  exact BoxTree.validC_splitE zoneCChunk063_valid zoneCChunk064_valid

def zoneCAssembly060 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).2
    zoneCChunk065 zoneCChunk066

theorem zoneCAssembly060_valid :
    zoneCAssembly060.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).2 = true := by
  unfold zoneCAssembly060
  exact BoxTree.validC_splitE zoneCChunk065_valid zoneCChunk066_valid

def zoneCAssembly061 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1
    zoneCAssembly059 zoneCAssembly060

theorem zoneCAssembly061_valid :
    zoneCAssembly061.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1 = true := by
  unfold zoneCAssembly061
  exact BoxTree.validC_splitK zoneCAssembly059_valid zoneCAssembly060_valid

def zoneCAssembly062 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2
    zoneCAssembly061 zoneCChunk067

theorem zoneCAssembly062_valid :
    zoneCAssembly062.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2 = true := by
  unfold zoneCAssembly062
  exact BoxTree.validC_splitE zoneCAssembly061_valid zoneCChunk067_valid

def zoneCAssembly063 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2
    zoneCAssembly058 zoneCAssembly062

theorem zoneCAssembly063_valid :
    zoneCAssembly063.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2 = true := by
  unfold zoneCAssembly063
  exact BoxTree.validC_splitK zoneCAssembly058_valid zoneCAssembly062_valid

def zoneCAssembly064 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2
    zoneCAssembly056 zoneCAssembly063

theorem zoneCAssembly064_valid :
    zoneCAssembly064.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly064
  exact BoxTree.validC_splitE zoneCAssembly056_valid zoneCAssembly063_valid

def zoneCAssembly065 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1
    zoneCAssembly031 zoneCAssembly064

theorem zoneCAssembly065_valid :
    zoneCAssembly065.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1 = true := by
  unfold zoneCAssembly065
  exact BoxTree.validC_splitK zoneCAssembly031_valid zoneCAssembly064_valid

def zoneCAssembly066 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).1
    zoneCChunk068 zoneCChunk069

theorem zoneCAssembly066_valid :
    zoneCAssembly066.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).1 = true := by
  unfold zoneCAssembly066
  exact BoxTree.validC_splitK zoneCChunk068_valid zoneCChunk069_valid

def zoneCAssembly067 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2
    zoneCChunk071 zoneCChunk072

theorem zoneCAssembly067_valid :
    zoneCAssembly067.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2 = true := by
  unfold zoneCAssembly067
  exact BoxTree.validC_splitE zoneCChunk071_valid zoneCChunk072_valid

def zoneCAssembly068 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1
    zoneCChunk070 zoneCAssembly067

theorem zoneCAssembly068_valid :
    zoneCAssembly068.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1 = true := by
  unfold zoneCAssembly068
  exact BoxTree.validC_splitK zoneCChunk070_valid zoneCAssembly067_valid

def zoneCAssembly069 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2
    zoneCAssembly068 zoneCChunk073

theorem zoneCAssembly069_valid :
    zoneCAssembly069.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2 = true := by
  unfold zoneCAssembly069
  exact BoxTree.validC_splitE zoneCAssembly068_valid zoneCChunk073_valid

def zoneCAssembly070 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2
    zoneCAssembly066 zoneCAssembly069

theorem zoneCAssembly070_valid :
    zoneCAssembly070.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2 = true := by
  unfold zoneCAssembly070
  exact BoxTree.validC_splitK zoneCAssembly066_valid zoneCAssembly069_valid

def zoneCAssembly071 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2
    zoneCAssembly065 zoneCAssembly070

theorem zoneCAssembly071_valid :
    zoneCAssembly071.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2 = true := by
  unfold zoneCAssembly071
  exact BoxTree.validC_splitE zoneCAssembly065_valid zoneCAssembly070_valid

def zoneCAssembly072 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1
    zoneCAssembly010 zoneCAssembly071

theorem zoneCAssembly072_valid :
    zoneCAssembly072.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly072
  exact BoxTree.validC_splitK zoneCAssembly010_valid zoneCAssembly071_valid

def zoneCAssembly073 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).1)).1)).1)).1
    zoneCChunk074 zoneCChunk075

theorem zoneCAssembly073_valid :
    zoneCAssembly073.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly073
  exact BoxTree.validC_splitE zoneCChunk074_valid zoneCChunk075_valid

def zoneCAssembly074 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).1)).1)).1)).2
    zoneCChunk076 zoneCChunk077

theorem zoneCAssembly074_valid :
    zoneCAssembly074.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).1)).1)).1)).2 = true := by
  unfold zoneCAssembly074
  exact BoxTree.validC_splitE zoneCChunk076_valid zoneCChunk077_valid

def zoneCAssembly075 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).1)).1)).1
    zoneCAssembly073 zoneCAssembly074

theorem zoneCAssembly075_valid :
    zoneCAssembly075.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly075
  exact BoxTree.validC_splitK zoneCAssembly073_valid zoneCAssembly074_valid

def zoneCAssembly076 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).1)).1)).2
    zoneCChunk078 zoneCChunk079

theorem zoneCAssembly076_valid :
    zoneCAssembly076.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).1)).1)).2 = true := by
  unfold zoneCAssembly076
  exact BoxTree.validC_splitK zoneCChunk078_valid zoneCChunk079_valid

def zoneCAssembly077 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).1)).1
    zoneCAssembly075 zoneCAssembly076

theorem zoneCAssembly077_valid :
    zoneCAssembly077.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly077
  exact BoxTree.validC_splitE zoneCAssembly075_valid zoneCAssembly076_valid

def zoneCAssembly078 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).1)).2)).1)).1
    zoneCChunk080 zoneCChunk081

theorem zoneCAssembly078_valid :
    zoneCAssembly078.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).1)).2)).1)).1 = true := by
  unfold zoneCAssembly078
  exact BoxTree.validC_splitE zoneCChunk080_valid zoneCChunk081_valid

def zoneCAssembly079 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).1)).2)).1
    zoneCAssembly078 zoneCChunk082

theorem zoneCAssembly079_valid :
    zoneCAssembly079.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).1)).2)).1 = true := by
  unfold zoneCAssembly079
  exact BoxTree.validC_splitK zoneCAssembly078_valid zoneCChunk082_valid

def zoneCAssembly080 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).1)).2)).2
    zoneCChunk083 zoneCChunk084

theorem zoneCAssembly080_valid :
    zoneCAssembly080.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).1)).2)).2 = true := by
  unfold zoneCAssembly080
  exact BoxTree.validC_splitK zoneCChunk083_valid zoneCChunk084_valid

def zoneCAssembly081 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).1)).2
    zoneCAssembly079 zoneCAssembly080

theorem zoneCAssembly081_valid :
    zoneCAssembly081.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).1)).2 = true := by
  unfold zoneCAssembly081
  exact BoxTree.validC_splitE zoneCAssembly079_valid zoneCAssembly080_valid

def zoneCAssembly082 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).1
    zoneCAssembly077 zoneCAssembly081

theorem zoneCAssembly082_valid :
    zoneCAssembly082.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly082
  exact BoxTree.validC_splitK zoneCAssembly077_valid zoneCAssembly081_valid

def zoneCAssembly083 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).2)).1)).1
    zoneCChunk085 zoneCChunk086

theorem zoneCAssembly083_valid :
    zoneCAssembly083.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).2)).1)).1 = true := by
  unfold zoneCAssembly083
  exact BoxTree.validC_splitK zoneCChunk085_valid zoneCChunk086_valid

def zoneCAssembly084 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).2)).1)).2
    zoneCChunk087 zoneCChunk088

theorem zoneCAssembly084_valid :
    zoneCAssembly084.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly084
  exact BoxTree.validC_splitK zoneCChunk087_valid zoneCChunk088_valid

def zoneCAssembly085 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).2)).1
    zoneCAssembly083 zoneCAssembly084

theorem zoneCAssembly085_valid :
    zoneCAssembly085.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).2)).1 = true := by
  unfold zoneCAssembly085
  exact BoxTree.validC_splitE zoneCAssembly083_valid zoneCAssembly084_valid

def zoneCAssembly086 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).2)).2
    zoneCChunk089 zoneCChunk090

theorem zoneCAssembly086_valid :
    zoneCAssembly086.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).2)).2 = true := by
  unfold zoneCAssembly086
  exact BoxTree.validC_splitE zoneCChunk089_valid zoneCChunk090_valid

def zoneCAssembly087 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).2
    zoneCAssembly085 zoneCAssembly086

theorem zoneCAssembly087_valid :
    zoneCAssembly087.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1)).2 = true := by
  unfold zoneCAssembly087
  exact BoxTree.validC_splitK zoneCAssembly085_valid zoneCAssembly086_valid

def zoneCAssembly088 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1
    zoneCAssembly082 zoneCAssembly087

theorem zoneCAssembly088_valid :
    zoneCAssembly088.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly088
  exact BoxTree.validC_splitE zoneCAssembly082_valid zoneCAssembly087_valid

def zoneCAssembly089 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).2)).2)).1
    zoneCChunk092 zoneCChunk093

theorem zoneCAssembly089_valid :
    zoneCAssembly089.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).2)).2)).1 = true := by
  unfold zoneCAssembly089
  exact BoxTree.validC_splitE zoneCChunk092_valid zoneCChunk093_valid

def zoneCAssembly090 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).2)).2
    zoneCAssembly089 zoneCChunk094

theorem zoneCAssembly090_valid :
    zoneCAssembly090.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).2)).2 = true := by
  unfold zoneCAssembly090
  exact BoxTree.validC_splitK zoneCAssembly089_valid zoneCChunk094_valid

def zoneCAssembly091 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).2
    zoneCChunk091 zoneCAssembly090

theorem zoneCAssembly091_valid :
    zoneCAssembly091.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1)).2 = true := by
  unfold zoneCAssembly091
  exact BoxTree.validC_splitE zoneCChunk091_valid zoneCAssembly090_valid

def zoneCAssembly092 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1
    zoneCAssembly088 zoneCAssembly091

theorem zoneCAssembly092_valid :
    zoneCAssembly092.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).1 = true := by
  unfold zoneCAssembly092
  exact BoxTree.validC_splitK zoneCAssembly088_valid zoneCAssembly091_valid

def zoneCAssembly093 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).1)).1)).1)).1
    zoneCChunk095 zoneCChunk096

theorem zoneCAssembly093_valid :
    zoneCAssembly093.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly093
  exact BoxTree.validC_splitE zoneCChunk095_valid zoneCChunk096_valid

def zoneCAssembly094 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).1)).1)).1)).2
    zoneCChunk097 zoneCChunk098

theorem zoneCAssembly094_valid :
    zoneCAssembly094.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).1)).1)).1)).2 = true := by
  unfold zoneCAssembly094
  exact BoxTree.validC_splitE zoneCChunk097_valid zoneCChunk098_valid

def zoneCAssembly095 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).1)).1)).1
    zoneCAssembly093 zoneCAssembly094

theorem zoneCAssembly095_valid :
    zoneCAssembly095.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).1)).1)).1 = true := by
  unfold zoneCAssembly095
  exact BoxTree.validC_splitK zoneCAssembly093_valid zoneCAssembly094_valid

def zoneCAssembly096 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).1)).1
    zoneCAssembly095 zoneCChunk099

theorem zoneCAssembly096_valid :
    zoneCAssembly096.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).1)).1 = true := by
  unfold zoneCAssembly096
  exact BoxTree.validC_splitE zoneCAssembly095_valid zoneCChunk099_valid

def zoneCAssembly097 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).1)).2)).1)).1
    zoneCChunk100 zoneCChunk101

theorem zoneCAssembly097_valid :
    zoneCAssembly097.validC (RatBox.splitE ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).1)).2)).1)).1 = true := by
  unfold zoneCAssembly097
  exact BoxTree.validC_splitK zoneCChunk100_valid zoneCChunk101_valid

def zoneCAssembly098 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).1)).2)).1)).2
    zoneCChunk102 zoneCChunk103

theorem zoneCAssembly098_valid :
    zoneCAssembly098.validC (RatBox.splitE ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly098
  exact BoxTree.validC_splitK zoneCChunk102_valid zoneCChunk103_valid

def zoneCAssembly099 : BoxTree :=
  .splitE (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).1)).2)).1
    zoneCAssembly097 zoneCAssembly098

theorem zoneCAssembly099_valid :
    zoneCAssembly099.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).1)).2)).1 = true := by
  unfold zoneCAssembly099
  exact BoxTree.validC_splitE zoneCAssembly097_valid zoneCAssembly098_valid

def zoneCAssembly100 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).1)).2
    zoneCAssembly099 zoneCChunk104

theorem zoneCAssembly100_valid :
    zoneCAssembly100.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly100
  exact BoxTree.validC_splitE zoneCAssembly099_valid zoneCChunk104_valid

def zoneCAssembly101 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).1
    zoneCAssembly096 zoneCAssembly100

theorem zoneCAssembly101_valid :
    zoneCAssembly101.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).1 = true := by
  unfold zoneCAssembly101
  exact BoxTree.validC_splitK zoneCAssembly096_valid zoneCAssembly100_valid

def zoneCAssembly102 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).2)).1)).1
    zoneCChunk105 zoneCChunk106

theorem zoneCAssembly102_valid :
    zoneCAssembly102.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).2)).1)).1 = true := by
  unfold zoneCAssembly102
  exact BoxTree.validC_splitE zoneCChunk105_valid zoneCChunk106_valid

def zoneCAssembly103 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).2)).1)).2
    zoneCChunk107 zoneCChunk108

theorem zoneCAssembly103_valid :
    zoneCAssembly103.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).2)).1)).2 = true := by
  unfold zoneCAssembly103
  exact BoxTree.validC_splitE zoneCChunk107_valid zoneCChunk108_valid

def zoneCAssembly104 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).2)).1
    zoneCAssembly102 zoneCAssembly103

theorem zoneCAssembly104_valid :
    zoneCAssembly104.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).2)).1 = true := by
  unfold zoneCAssembly104
  exact BoxTree.validC_splitK zoneCAssembly102_valid zoneCAssembly103_valid

def zoneCAssembly105 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).2)).2
    zoneCChunk109 zoneCChunk110

theorem zoneCAssembly105_valid :
    zoneCAssembly105.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).2)).2 = true := by
  unfold zoneCAssembly105
  exact BoxTree.validC_splitK zoneCChunk109_valid zoneCChunk110_valid

def zoneCAssembly106 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).2
    zoneCAssembly104 zoneCAssembly105

theorem zoneCAssembly106_valid :
    zoneCAssembly106.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2)).2 = true := by
  unfold zoneCAssembly106
  exact BoxTree.validC_splitE zoneCAssembly104_valid zoneCAssembly105_valid

def zoneCAssembly107 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2
    zoneCAssembly101 zoneCAssembly106

theorem zoneCAssembly107_valid :
    zoneCAssembly107.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1)).2 = true := by
  unfold zoneCAssembly107
  exact BoxTree.validC_splitK zoneCAssembly101_valid zoneCAssembly106_valid

def zoneCAssembly108 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1
    zoneCAssembly092 zoneCAssembly107

theorem zoneCAssembly108_valid :
    zoneCAssembly108.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).1 = true := by
  unfold zoneCAssembly108
  exact BoxTree.validC_splitE zoneCAssembly092_valid zoneCAssembly107_valid

def zoneCAssembly109 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).1)).1
    zoneCChunk112 zoneCChunk113

theorem zoneCAssembly109_valid :
    zoneCAssembly109.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).1)).1 = true := by
  unfold zoneCAssembly109
  exact BoxTree.validC_splitK zoneCChunk112_valid zoneCChunk113_valid

def zoneCAssembly110 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).1
    zoneCAssembly109 zoneCChunk114

theorem zoneCAssembly110_valid :
    zoneCAssembly110.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).1 = true := by
  unfold zoneCAssembly110
  exact BoxTree.validC_splitE zoneCAssembly109_valid zoneCChunk114_valid

def zoneCAssembly111 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2
    zoneCAssembly110 zoneCChunk115

theorem zoneCAssembly111_valid :
    zoneCAssembly111.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2 = true := by
  unfold zoneCAssembly111
  exact BoxTree.validC_splitK zoneCAssembly110_valid zoneCChunk115_valid

def zoneCAssembly112 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2
    zoneCChunk111 zoneCAssembly111

theorem zoneCAssembly112_valid :
    zoneCAssembly112.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly112
  exact BoxTree.validC_splitE zoneCChunk111_valid zoneCAssembly111_valid

def zoneCAssembly113 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1
    zoneCAssembly108 zoneCAssembly112

theorem zoneCAssembly113_valid :
    zoneCAssembly113.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1 = true := by
  unfold zoneCAssembly113
  exact BoxTree.validC_splitK zoneCAssembly108_valid zoneCAssembly112_valid

def zoneCAssembly114 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).1)).1)).1)).1
    zoneCChunk116 zoneCChunk117

theorem zoneCAssembly114_valid :
    zoneCAssembly114.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly114
  exact BoxTree.validC_splitE zoneCChunk116_valid zoneCChunk117_valid

def zoneCAssembly115 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).1)).1)).1)).2
    zoneCChunk118 zoneCChunk119

theorem zoneCAssembly115_valid :
    zoneCAssembly115.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).1)).1)).1)).2 = true := by
  unfold zoneCAssembly115
  exact BoxTree.validC_splitE zoneCChunk118_valid zoneCChunk119_valid

def zoneCAssembly116 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).1)).1)).1
    zoneCAssembly114 zoneCAssembly115

theorem zoneCAssembly116_valid :
    zoneCAssembly116.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).1)).1)).1 = true := by
  unfold zoneCAssembly116
  exact BoxTree.validC_splitK zoneCAssembly114_valid zoneCAssembly115_valid

def zoneCAssembly117 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).1)).1
    zoneCAssembly116 zoneCChunk120

theorem zoneCAssembly117_valid :
    zoneCAssembly117.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).1)).1 = true := by
  unfold zoneCAssembly117
  exact BoxTree.validC_splitE zoneCAssembly116_valid zoneCChunk120_valid

def zoneCAssembly118 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).1)).2)).1)).1
    zoneCChunk121 zoneCChunk122

theorem zoneCAssembly118_valid :
    zoneCAssembly118.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).1)).2)).1)).1 = true := by
  unfold zoneCAssembly118
  exact BoxTree.validC_splitE zoneCChunk121_valid zoneCChunk122_valid

def zoneCAssembly119 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).1)).2)).1)).2
    zoneCChunk123 zoneCChunk124

theorem zoneCAssembly119_valid :
    zoneCAssembly119.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly119
  exact BoxTree.validC_splitE zoneCChunk123_valid zoneCChunk124_valid

def zoneCAssembly120 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).1)).2)).1
    zoneCAssembly118 zoneCAssembly119

theorem zoneCAssembly120_valid :
    zoneCAssembly120.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).1)).2)).1 = true := by
  unfold zoneCAssembly120
  exact BoxTree.validC_splitK zoneCAssembly118_valid zoneCAssembly119_valid

def zoneCAssembly121 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).1)).2
    zoneCAssembly120 zoneCChunk125

theorem zoneCAssembly121_valid :
    zoneCAssembly121.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).1)).2 = true := by
  unfold zoneCAssembly121
  exact BoxTree.validC_splitE zoneCAssembly120_valid zoneCChunk125_valid

def zoneCAssembly122 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).1
    zoneCAssembly117 zoneCAssembly121

theorem zoneCAssembly122_valid :
    zoneCAssembly122.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).1 = true := by
  unfold zoneCAssembly122
  exact BoxTree.validC_splitK zoneCAssembly117_valid zoneCAssembly121_valid

def zoneCAssembly123 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).1)).2
    zoneCChunk127 zoneCChunk128

theorem zoneCAssembly123_valid :
    zoneCAssembly123.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).1)).2 = true := by
  unfold zoneCAssembly123
  exact BoxTree.validC_splitK zoneCChunk127_valid zoneCChunk128_valid

def zoneCAssembly124 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).1
    zoneCChunk126 zoneCAssembly123

theorem zoneCAssembly124_valid :
    zoneCAssembly124.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).1 = true := by
  unfold zoneCAssembly124
  exact BoxTree.validC_splitE zoneCChunk126_valid zoneCAssembly123_valid

def zoneCAssembly125 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2
    zoneCChunk129 zoneCChunk130

theorem zoneCAssembly125_valid :
    zoneCAssembly125.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2 = true := by
  unfold zoneCAssembly125
  exact BoxTree.validC_splitE zoneCChunk129_valid zoneCChunk130_valid

def zoneCAssembly126 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1
    zoneCAssembly124 zoneCAssembly125

theorem zoneCAssembly126_valid :
    zoneCAssembly126.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1 = true := by
  unfold zoneCAssembly126
  exact BoxTree.validC_splitK zoneCAssembly124_valid zoneCAssembly125_valid

def zoneCAssembly127 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).1
    zoneCChunk131 zoneCChunk132

theorem zoneCAssembly127_valid :
    zoneCAssembly127.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).1 = true := by
  unfold zoneCAssembly127
  exact BoxTree.validC_splitK zoneCChunk131_valid zoneCChunk132_valid

def zoneCAssembly128 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2
    zoneCAssembly127 zoneCChunk133

theorem zoneCAssembly128_valid :
    zoneCAssembly128.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2 = true := by
  unfold zoneCAssembly128
  exact BoxTree.validC_splitK zoneCAssembly127_valid zoneCChunk133_valid

def zoneCAssembly129 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2
    zoneCAssembly126 zoneCAssembly128

theorem zoneCAssembly129_valid :
    zoneCAssembly129.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2 = true := by
  unfold zoneCAssembly129
  exact BoxTree.validC_splitE zoneCAssembly126_valid zoneCAssembly128_valid

def zoneCAssembly130 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2
    zoneCAssembly122 zoneCAssembly129

theorem zoneCAssembly130_valid :
    zoneCAssembly130.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2 = true := by
  unfold zoneCAssembly130
  exact BoxTree.validC_splitK zoneCAssembly122_valid zoneCAssembly129_valid

def zoneCAssembly131 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2
    zoneCAssembly113 zoneCAssembly130

theorem zoneCAssembly131_valid :
    zoneCAssembly131.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2 = true := by
  unfold zoneCAssembly131
  exact BoxTree.validC_splitE zoneCAssembly113_valid zoneCAssembly130_valid

def zoneCAssembly132 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1
    zoneCAssembly072 zoneCAssembly131

theorem zoneCAssembly132_valid :
    zoneCAssembly132.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly132
  exact BoxTree.validC_splitK zoneCAssembly072_valid zoneCAssembly131_valid

def zoneCAssembly133 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).1)).1)).2
    zoneCChunk136 zoneCChunk137

theorem zoneCAssembly133_valid :
    zoneCAssembly133.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).1)).1)).2 = true := by
  unfold zoneCAssembly133
  exact BoxTree.validC_splitK zoneCChunk136_valid zoneCChunk137_valid

def zoneCAssembly134 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).1)).1
    zoneCChunk135 zoneCAssembly133

theorem zoneCAssembly134_valid :
    zoneCAssembly134.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).1)).1 = true := by
  unfold zoneCAssembly134
  exact BoxTree.validC_splitE zoneCChunk135_valid zoneCAssembly133_valid

def zoneCAssembly135 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).1
    zoneCAssembly134 zoneCChunk138

theorem zoneCAssembly135_valid :
    zoneCAssembly135.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).1 = true := by
  unfold zoneCAssembly135
  exact BoxTree.validC_splitK zoneCAssembly134_valid zoneCChunk138_valid

def zoneCAssembly136 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2
    zoneCAssembly135 zoneCChunk139

theorem zoneCAssembly136_valid :
    zoneCAssembly136.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2 = true := by
  unfold zoneCAssembly136
  exact BoxTree.validC_splitK zoneCAssembly135_valid zoneCChunk139_valid

def zoneCAssembly137 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).2
    zoneCChunk134 zoneCAssembly136

theorem zoneCAssembly137_valid :
    zoneCAssembly137.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1)).2 = true := by
  unfold zoneCAssembly137
  exact BoxTree.validC_splitE zoneCChunk134_valid zoneCAssembly136_valid

def zoneCAssembly138 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1
    zoneCAssembly132 zoneCAssembly137

theorem zoneCAssembly138_valid :
    zoneCAssembly138.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly138
  exact BoxTree.validC_splitK zoneCAssembly132_valid zoneCAssembly137_valid

def zoneCAssembly139 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1
    zoneCAssembly138 zoneCChunk140

theorem zoneCAssembly139_valid :
    zoneCAssembly139.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly139
  exact BoxTree.validC_splitK zoneCAssembly138_valid zoneCChunk140_valid

def zoneCAssembly140 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1
    zoneCAssembly139 zoneCChunk141

theorem zoneCAssembly140_valid :
    zoneCAssembly140.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly140
  exact BoxTree.validC_splitK zoneCAssembly139_valid zoneCChunk141_valid

def zoneCAssembly141 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1
    zoneCAssembly140 zoneCChunk142

theorem zoneCAssembly141_valid :
    zoneCAssembly141.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly141
  exact BoxTree.validC_splitK zoneCAssembly140_valid zoneCChunk142_valid

def zoneCAssembly142 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1
    zoneCAssembly141 zoneCChunk143

theorem zoneCAssembly142_valid :
    zoneCAssembly142.validC (RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly142
  exact BoxTree.validC_splitK zoneCAssembly141_valid zoneCChunk143_valid

def zoneCAssembly143 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).1)).1)).2
    zoneCChunk145 zoneCChunk146

theorem zoneCAssembly143_valid :
    zoneCAssembly143.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).1)).1)).2 = true := by
  unfold zoneCAssembly143
  exact BoxTree.validC_splitK zoneCChunk145_valid zoneCChunk146_valid

def zoneCAssembly144 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).1)).1
    zoneCChunk144 zoneCAssembly143

theorem zoneCAssembly144_valid :
    zoneCAssembly144.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly144
  exact BoxTree.validC_splitK zoneCChunk144_valid zoneCAssembly143_valid

def zoneCAssembly145 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).1)).2)).1)).1)).2
    zoneCChunk148 zoneCChunk149

theorem zoneCAssembly145_valid :
    zoneCAssembly145.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).1)).2)).1)).1)).2 = true := by
  unfold zoneCAssembly145
  exact BoxTree.validC_splitE zoneCChunk148_valid zoneCChunk149_valid

def zoneCAssembly146 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).1)).2)).1)).1
    zoneCChunk147 zoneCAssembly145

theorem zoneCAssembly146_valid :
    zoneCAssembly146.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).1)).2)).1)).1 = true := by
  unfold zoneCAssembly146
  exact BoxTree.validC_splitK zoneCChunk147_valid zoneCAssembly145_valid

def zoneCAssembly147 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).1)).2)).1
    zoneCAssembly146 zoneCChunk150

theorem zoneCAssembly147_valid :
    zoneCAssembly147.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).1)).2)).1 = true := by
  unfold zoneCAssembly147
  exact BoxTree.validC_splitE zoneCAssembly146_valid zoneCChunk150_valid

def zoneCAssembly148 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).1)).2)).2)).1)).1
    zoneCChunk151 zoneCChunk152

theorem zoneCAssembly148_valid :
    zoneCAssembly148.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).1)).2)).2)).1)).1 = true := by
  unfold zoneCAssembly148
  exact BoxTree.validC_splitE zoneCChunk151_valid zoneCChunk152_valid

def zoneCAssembly149 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).1)).2)).2)).1)).2
    zoneCChunk153 zoneCChunk154

theorem zoneCAssembly149_valid :
    zoneCAssembly149.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).1)).2)).2)).1)).2 = true := by
  unfold zoneCAssembly149
  exact BoxTree.validC_splitE zoneCChunk153_valid zoneCChunk154_valid

def zoneCAssembly150 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).1)).2)).2)).1
    zoneCAssembly148 zoneCAssembly149

theorem zoneCAssembly150_valid :
    zoneCAssembly150.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).1)).2)).2)).1 = true := by
  unfold zoneCAssembly150
  exact BoxTree.validC_splitK zoneCAssembly148_valid zoneCAssembly149_valid

def zoneCAssembly151 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).1)).2)).2
    zoneCAssembly150 zoneCChunk155

theorem zoneCAssembly151_valid :
    zoneCAssembly151.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).1)).2)).2 = true := by
  unfold zoneCAssembly151
  exact BoxTree.validC_splitE zoneCAssembly150_valid zoneCChunk155_valid

def zoneCAssembly152 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).1)).2
    zoneCAssembly147 zoneCAssembly151

theorem zoneCAssembly152_valid :
    zoneCAssembly152.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).1)).2 = true := by
  unfold zoneCAssembly152
  exact BoxTree.validC_splitK zoneCAssembly147_valid zoneCAssembly151_valid

def zoneCAssembly153 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).1
    zoneCAssembly144 zoneCAssembly152

theorem zoneCAssembly153_valid :
    zoneCAssembly153.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly153
  exact BoxTree.validC_splitK zoneCAssembly144_valid zoneCAssembly152_valid

def zoneCAssembly154 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).2)).1)).1)).1
    zoneCChunk156 zoneCChunk157

theorem zoneCAssembly154_valid :
    zoneCAssembly154.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).2)).1)).1)).1 = true := by
  unfold zoneCAssembly154
  exact BoxTree.validC_splitE zoneCChunk156_valid zoneCChunk157_valid

def zoneCAssembly155 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).2)).1)).1)).2
    zoneCChunk158 zoneCChunk159

theorem zoneCAssembly155_valid :
    zoneCAssembly155.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).2)).1)).1)).2 = true := by
  unfold zoneCAssembly155
  exact BoxTree.validC_splitE zoneCChunk158_valid zoneCChunk159_valid

def zoneCAssembly156 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).2)).1)).1
    zoneCAssembly154 zoneCAssembly155

theorem zoneCAssembly156_valid :
    zoneCAssembly156.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).2)).1)).1 = true := by
  unfold zoneCAssembly156
  exact BoxTree.validC_splitK zoneCAssembly154_valid zoneCAssembly155_valid

def zoneCAssembly157 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).2)).1)).2
    zoneCChunk160 zoneCChunk161

theorem zoneCAssembly157_valid :
    zoneCAssembly157.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly157
  exact BoxTree.validC_splitK zoneCChunk160_valid zoneCChunk161_valid

def zoneCAssembly158 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).2)).1
    zoneCAssembly156 zoneCAssembly157

theorem zoneCAssembly158_valid :
    zoneCAssembly158.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).2)).1 = true := by
  unfold zoneCAssembly158
  exact BoxTree.validC_splitE zoneCAssembly156_valid zoneCAssembly157_valid

def zoneCAssembly159 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).2)).2
    zoneCChunk162 zoneCChunk163

theorem zoneCAssembly159_valid :
    zoneCAssembly159.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).2)).2 = true := by
  unfold zoneCAssembly159
  exact BoxTree.validC_splitE zoneCChunk162_valid zoneCChunk163_valid

def zoneCAssembly160 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).2
    zoneCAssembly158 zoneCAssembly159

theorem zoneCAssembly160_valid :
    zoneCAssembly160.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1)).2 = true := by
  unfold zoneCAssembly160
  exact BoxTree.validC_splitK zoneCAssembly158_valid zoneCAssembly159_valid

def zoneCAssembly161 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1
    zoneCAssembly153 zoneCAssembly160

theorem zoneCAssembly161_valid :
    zoneCAssembly161.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly161
  exact BoxTree.validC_splitK zoneCAssembly153_valid zoneCAssembly160_valid

def zoneCAssembly162 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1
    zoneCAssembly161 zoneCChunk164

theorem zoneCAssembly162_valid :
    zoneCAssembly162.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1)).1 = true := by
  unfold zoneCAssembly162
  exact BoxTree.validC_splitK zoneCAssembly161_valid zoneCChunk164_valid

def zoneCAssembly163 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1
    zoneCAssembly162 zoneCChunk165

theorem zoneCAssembly163_valid :
    zoneCAssembly163.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1)).1 = true := by
  unfold zoneCAssembly163
  exact BoxTree.validC_splitK zoneCAssembly162_valid zoneCChunk165_valid

def zoneCAssembly164 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1
    zoneCAssembly163 zoneCChunk166

theorem zoneCAssembly164_valid :
    zoneCAssembly164.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2)).1 = true := by
  unfold zoneCAssembly164
  exact BoxTree.validC_splitK zoneCAssembly163_valid zoneCChunk166_valid

def zoneCAssembly165 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2
    zoneCAssembly164 zoneCChunk167

theorem zoneCAssembly165_valid :
    zoneCAssembly165.validC (RatBox.splitE ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1)).2 = true := by
  unfold zoneCAssembly165
  exact BoxTree.validC_splitK zoneCAssembly164_valid zoneCChunk167_valid

def zoneCAssembly166 : BoxTree :=
  .splitE (RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1
    zoneCAssembly142 zoneCAssembly165

theorem zoneCAssembly166_valid :
    zoneCAssembly166.validC (RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).1 = true := by
  unfold zoneCAssembly166
  exact BoxTree.validC_splitE zoneCAssembly142_valid zoneCAssembly165_valid

def zoneCAssembly167 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).2)).1)).1)).1)).1)).1)).2
    zoneCChunk169 zoneCChunk170

theorem zoneCAssembly167_valid :
    zoneCAssembly167.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).2)).1)).1)).1)).1)).1)).2 = true := by
  unfold zoneCAssembly167
  exact BoxTree.validC_splitK zoneCChunk169_valid zoneCChunk170_valid

def zoneCAssembly168 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).2)).1)).1)).1)).1)).1
    zoneCChunk168 zoneCAssembly167

theorem zoneCAssembly168_valid :
    zoneCAssembly168.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).2)).1)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly168
  exact BoxTree.validC_splitK zoneCChunk168_valid zoneCAssembly167_valid

def zoneCAssembly169 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).2)).1)).1)).1)).1)).2)).1)).1
    zoneCChunk171 zoneCChunk172

theorem zoneCAssembly169_valid :
    zoneCAssembly169.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).2)).1)).1)).1)).1)).2)).1)).1 = true := by
  unfold zoneCAssembly169
  exact BoxTree.validC_splitK zoneCChunk171_valid zoneCChunk172_valid

def zoneCAssembly170 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).2)).1)).1)).1)).1)).2)).1
    zoneCAssembly169 zoneCChunk173

theorem zoneCAssembly170_valid :
    zoneCAssembly170.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).2)).1)).1)).1)).1)).2)).1 = true := by
  unfold zoneCAssembly170
  exact BoxTree.validC_splitE zoneCAssembly169_valid zoneCChunk173_valid

def zoneCAssembly171 : BoxTree :=
  .splitE (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).2)).1)).1)).1)).1)).2)).2)).1
    zoneCChunk174 zoneCChunk175

theorem zoneCAssembly171_valid :
    zoneCAssembly171.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).2)).1)).1)).1)).1)).2)).2)).1 = true := by
  unfold zoneCAssembly171
  exact BoxTree.validC_splitE zoneCChunk174_valid zoneCChunk175_valid

def zoneCAssembly172 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).2)).1)).1)).1)).1)).2)).2
    zoneCAssembly171 zoneCChunk176

theorem zoneCAssembly172_valid :
    zoneCAssembly172.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).2)).1)).1)).1)).1)).2)).2 = true := by
  unfold zoneCAssembly172
  exact BoxTree.validC_splitE zoneCAssembly171_valid zoneCChunk176_valid

def zoneCAssembly173 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).2)).1)).1)).1)).1)).2
    zoneCAssembly170 zoneCAssembly172

theorem zoneCAssembly173_valid :
    zoneCAssembly173.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).2)).1)).1)).1)).1)).2 = true := by
  unfold zoneCAssembly173
  exact BoxTree.validC_splitK zoneCAssembly170_valid zoneCAssembly172_valid

def zoneCAssembly174 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).2)).1)).1)).1)).1
    zoneCAssembly168 zoneCAssembly173

theorem zoneCAssembly174_valid :
    zoneCAssembly174.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).2)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly174
  exact BoxTree.validC_splitK zoneCAssembly168_valid zoneCAssembly173_valid

def zoneCAssembly175 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).2)).1)).1)).1)).2)).1
    zoneCChunk177 zoneCChunk178

theorem zoneCAssembly175_valid :
    zoneCAssembly175.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).2)).1)).1)).1)).2)).1 = true := by
  unfold zoneCAssembly175
  exact BoxTree.validC_splitE zoneCChunk177_valid zoneCChunk178_valid

def zoneCAssembly176 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).2)).1)).1)).1)).2
    zoneCAssembly175 zoneCChunk179

theorem zoneCAssembly176_valid :
    zoneCAssembly176.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).2)).1)).1)).1)).2 = true := by
  unfold zoneCAssembly176
  exact BoxTree.validC_splitK zoneCAssembly175_valid zoneCChunk179_valid

def zoneCAssembly177 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).2)).1)).1)).1
    zoneCAssembly174 zoneCAssembly176

theorem zoneCAssembly177_valid :
    zoneCAssembly177.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).2)).1)).1)).1 = true := by
  unfold zoneCAssembly177
  exact BoxTree.validC_splitK zoneCAssembly174_valid zoneCAssembly176_valid

def zoneCAssembly178 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).2)).1)).1
    zoneCAssembly177 zoneCChunk180

theorem zoneCAssembly178_valid :
    zoneCAssembly178.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).2)).1)).1 = true := by
  unfold zoneCAssembly178
  exact BoxTree.validC_splitK zoneCAssembly177_valid zoneCChunk180_valid

def zoneCAssembly179 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).2)).1
    zoneCAssembly178 zoneCChunk181

theorem zoneCAssembly179_valid :
    zoneCAssembly179.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).2)).1 = true := by
  unfold zoneCAssembly179
  exact BoxTree.validC_splitK zoneCAssembly178_valid zoneCChunk181_valid

def zoneCAssembly180 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).2
    zoneCAssembly179 zoneCChunk182

theorem zoneCAssembly180_valid :
    zoneCAssembly180.validC (RatBox.splitE ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1)).2 = true := by
  unfold zoneCAssembly180
  exact BoxTree.validC_splitK zoneCAssembly179_valid zoneCChunk182_valid

def zoneCAssembly181 : BoxTree :=
  .splitE (RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1
    zoneCAssembly166 zoneCAssembly180

theorem zoneCAssembly181_valid :
    zoneCAssembly181.validC (RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).1 = true := by
  unfold zoneCAssembly181
  exact BoxTree.validC_splitE zoneCAssembly166_valid zoneCAssembly180_valid

def zoneCAssembly182 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).2)).1)).1)).1)).1)).2
    zoneCChunk184 zoneCChunk185

theorem zoneCAssembly182_valid :
    zoneCAssembly182.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).2)).1)).1)).1)).1)).2 = true := by
  unfold zoneCAssembly182
  exact BoxTree.validC_splitK zoneCChunk184_valid zoneCChunk185_valid

def zoneCAssembly183 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).2)).1)).1)).1)).1
    zoneCChunk183 zoneCAssembly182

theorem zoneCAssembly183_valid :
    zoneCAssembly183.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).2)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly183
  exact BoxTree.validC_splitK zoneCChunk183_valid zoneCAssembly182_valid

def zoneCAssembly184 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).2)).1)).1)).1
    zoneCAssembly183 zoneCChunk186

theorem zoneCAssembly184_valid :
    zoneCAssembly184.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).2)).1)).1)).1 = true := by
  unfold zoneCAssembly184
  exact BoxTree.validC_splitK zoneCAssembly183_valid zoneCChunk186_valid

def zoneCAssembly185 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).2)).1)).1
    zoneCAssembly184 zoneCChunk187

theorem zoneCAssembly185_valid :
    zoneCAssembly185.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).2)).1)).1 = true := by
  unfold zoneCAssembly185
  exact BoxTree.validC_splitK zoneCAssembly184_valid zoneCChunk187_valid

def zoneCAssembly186 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).2)).1
    zoneCAssembly185 zoneCChunk188

theorem zoneCAssembly186_valid :
    zoneCAssembly186.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).2)).1 = true := by
  unfold zoneCAssembly186
  exact BoxTree.validC_splitK zoneCAssembly185_valid zoneCChunk188_valid

def zoneCAssembly187 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).2
    zoneCAssembly186 zoneCChunk189

theorem zoneCAssembly187_valid :
    zoneCAssembly187.validC (RatBox.splitE ((RatBox.splitE (zoneCRoot)).1)).2 = true := by
  unfold zoneCAssembly187
  exact BoxTree.validC_splitK zoneCAssembly186_valid zoneCChunk189_valid

def zoneCAssembly188 : BoxTree :=
  .splitE (RatBox.splitE (zoneCRoot)).1
    zoneCAssembly181 zoneCAssembly187

theorem zoneCAssembly188_valid :
    zoneCAssembly188.validC (RatBox.splitE (zoneCRoot)).1 = true := by
  unfold zoneCAssembly188
  exact BoxTree.validC_splitE zoneCAssembly181_valid zoneCAssembly187_valid

def zoneCAssembly189 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2)).2)).2
    zoneCChunk196 zoneCChunk197

theorem zoneCAssembly189_valid :
    zoneCAssembly189.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2)).2)).2 = true := by
  unfold zoneCAssembly189
  exact BoxTree.validC_splitK zoneCChunk196_valid zoneCChunk197_valid

def zoneCAssembly190 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2)).2
    zoneCChunk195 zoneCAssembly189

theorem zoneCAssembly190_valid :
    zoneCAssembly190.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2)).2 = true := by
  unfold zoneCAssembly190
  exact BoxTree.validC_splitE zoneCChunk195_valid zoneCAssembly189_valid

def zoneCAssembly191 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2
    zoneCChunk194 zoneCAssembly190

theorem zoneCAssembly191_valid :
    zoneCAssembly191.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2 = true := by
  unfold zoneCAssembly191
  exact BoxTree.validC_splitK zoneCChunk194_valid zoneCAssembly190_valid

def zoneCAssembly192 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1
    zoneCChunk193 zoneCAssembly191

theorem zoneCAssembly192_valid :
    zoneCAssembly192.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1 = true := by
  unfold zoneCAssembly192
  exact BoxTree.validC_splitE zoneCChunk193_valid zoneCAssembly191_valid

def zoneCAssembly193 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1)).2)).1)).2
    zoneCChunk201 zoneCChunk202

theorem zoneCAssembly193_valid :
    zoneCAssembly193.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly193
  exact BoxTree.validC_splitK zoneCChunk201_valid zoneCChunk202_valid

def zoneCAssembly194 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1)).2)).1
    zoneCChunk200 zoneCAssembly193

theorem zoneCAssembly194_valid :
    zoneCAssembly194.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1)).2)).1 = true := by
  unfold zoneCAssembly194
  exact BoxTree.validC_splitE zoneCChunk200_valid zoneCAssembly193_valid

def zoneCAssembly195 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1)).2)).2)).2)).1
    zoneCChunk204 zoneCChunk205

theorem zoneCAssembly195_valid :
    zoneCAssembly195.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1)).2)).2)).2)).1 = true := by
  unfold zoneCAssembly195
  exact BoxTree.validC_splitE zoneCChunk204_valid zoneCChunk205_valid

def zoneCAssembly196 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1)).2)).2)).2)).2)).2
    zoneCChunk207 zoneCChunk208

theorem zoneCAssembly196_valid :
    zoneCAssembly196.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1)).2)).2)).2)).2)).2 = true := by
  unfold zoneCAssembly196
  exact BoxTree.validC_splitK zoneCChunk207_valid zoneCChunk208_valid

def zoneCAssembly197 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1)).2)).2)).2)).2
    zoneCChunk206 zoneCAssembly196

theorem zoneCAssembly197_valid :
    zoneCAssembly197.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1)).2)).2)).2)).2 = true := by
  unfold zoneCAssembly197
  exact BoxTree.validC_splitE zoneCChunk206_valid zoneCAssembly196_valid

def zoneCAssembly198 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1)).2)).2)).2
    zoneCAssembly195 zoneCAssembly197

theorem zoneCAssembly198_valid :
    zoneCAssembly198.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1)).2)).2)).2 = true := by
  unfold zoneCAssembly198
  exact BoxTree.validC_splitK zoneCAssembly195_valid zoneCAssembly197_valid

def zoneCAssembly199 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1)).2)).2
    zoneCChunk203 zoneCAssembly198

theorem zoneCAssembly199_valid :
    zoneCAssembly199.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1)).2)).2 = true := by
  unfold zoneCAssembly199
  exact BoxTree.validC_splitE zoneCChunk203_valid zoneCAssembly198_valid

def zoneCAssembly200 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1)).2
    zoneCAssembly194 zoneCAssembly199

theorem zoneCAssembly200_valid :
    zoneCAssembly200.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1)).2 = true := by
  unfold zoneCAssembly200
  exact BoxTree.validC_splitK zoneCAssembly194_valid zoneCAssembly199_valid

def zoneCAssembly201 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1
    zoneCChunk199 zoneCAssembly200

theorem zoneCAssembly201_valid :
    zoneCAssembly201.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1 = true := by
  unfold zoneCAssembly201
  exact BoxTree.validC_splitE zoneCChunk199_valid zoneCAssembly200_valid

def zoneCAssembly202 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2)).2)).1)).2)).1)).2
    zoneCChunk212 zoneCChunk213

theorem zoneCAssembly202_valid :
    zoneCAssembly202.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2)).2)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly202
  exact BoxTree.validC_splitK zoneCChunk212_valid zoneCChunk213_valid

def zoneCAssembly203 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2)).2)).1)).2)).1
    zoneCChunk211 zoneCAssembly202

theorem zoneCAssembly203_valid :
    zoneCAssembly203.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2)).2)).1)).2)).1 = true := by
  unfold zoneCAssembly203
  exact BoxTree.validC_splitE zoneCChunk211_valid zoneCAssembly202_valid

def zoneCAssembly204 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2)).2)).1)).2)).2)).2
    zoneCChunk215 zoneCChunk216

theorem zoneCAssembly204_valid :
    zoneCAssembly204.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2)).2)).1)).2)).2)).2 = true := by
  unfold zoneCAssembly204
  exact BoxTree.validC_splitK zoneCChunk215_valid zoneCChunk216_valid

def zoneCAssembly205 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2)).2)).1)).2)).2
    zoneCChunk214 zoneCAssembly204

theorem zoneCAssembly205_valid :
    zoneCAssembly205.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2)).2)).1)).2)).2 = true := by
  unfold zoneCAssembly205
  exact BoxTree.validC_splitE zoneCChunk214_valid zoneCAssembly204_valid

def zoneCAssembly206 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2)).2)).1)).2
    zoneCAssembly203 zoneCAssembly205

theorem zoneCAssembly206_valid :
    zoneCAssembly206.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2)).2)).1)).2 = true := by
  unfold zoneCAssembly206
  exact BoxTree.validC_splitK zoneCAssembly203_valid zoneCAssembly205_valid

def zoneCAssembly207 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2)).2)).1
    zoneCChunk210 zoneCAssembly206

theorem zoneCAssembly207_valid :
    zoneCAssembly207.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2)).2)).1 = true := by
  unfold zoneCAssembly207
  exact BoxTree.validC_splitE zoneCChunk210_valid zoneCAssembly206_valid

def zoneCAssembly208 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2)).2)).2)).2)).1)).2
    zoneCChunk219 zoneCChunk220

theorem zoneCAssembly208_valid :
    zoneCAssembly208.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2)).2)).2)).2)).1)).2 = true := by
  unfold zoneCAssembly208
  exact BoxTree.validC_splitK zoneCChunk219_valid zoneCChunk220_valid

def zoneCAssembly209 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2)).2)).2)).2)).1
    zoneCChunk218 zoneCAssembly208

theorem zoneCAssembly209_valid :
    zoneCAssembly209.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2)).2)).2)).2)).1 = true := by
  unfold zoneCAssembly209
  exact BoxTree.validC_splitE zoneCChunk218_valid zoneCAssembly208_valid

def zoneCAssembly210 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2)).2)).2)).2)).2)).2
    zoneCChunk222 zoneCChunk223

theorem zoneCAssembly210_valid :
    zoneCAssembly210.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2)).2)).2)).2)).2)).2 = true := by
  unfold zoneCAssembly210
  exact BoxTree.validC_splitK zoneCChunk222_valid zoneCChunk223_valid

def zoneCAssembly211 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2)).2)).2)).2)).2
    zoneCChunk221 zoneCAssembly210

theorem zoneCAssembly211_valid :
    zoneCAssembly211.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2)).2)).2)).2)).2 = true := by
  unfold zoneCAssembly211
  exact BoxTree.validC_splitE zoneCChunk221_valid zoneCAssembly210_valid

def zoneCAssembly212 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2)).2)).2)).2
    zoneCAssembly209 zoneCAssembly211

theorem zoneCAssembly212_valid :
    zoneCAssembly212.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2)).2)).2)).2 = true := by
  unfold zoneCAssembly212
  exact BoxTree.validC_splitK zoneCAssembly209_valid zoneCAssembly211_valid

def zoneCAssembly213 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2)).2)).2
    zoneCChunk217 zoneCAssembly212

theorem zoneCAssembly213_valid :
    zoneCAssembly213.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2)).2)).2 = true := by
  unfold zoneCAssembly213
  exact BoxTree.validC_splitE zoneCChunk217_valid zoneCAssembly212_valid

def zoneCAssembly214 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2)).2
    zoneCAssembly207 zoneCAssembly213

theorem zoneCAssembly214_valid :
    zoneCAssembly214.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2)).2 = true := by
  unfold zoneCAssembly214
  exact BoxTree.validC_splitK zoneCAssembly207_valid zoneCAssembly213_valid

def zoneCAssembly215 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2
    zoneCChunk209 zoneCAssembly214

theorem zoneCAssembly215_valid :
    zoneCAssembly215.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2 = true := by
  unfold zoneCAssembly215
  exact BoxTree.validC_splitE zoneCChunk209_valid zoneCAssembly214_valid

def zoneCAssembly216 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2
    zoneCAssembly201 zoneCAssembly215

theorem zoneCAssembly216_valid :
    zoneCAssembly216.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2 = true := by
  unfold zoneCAssembly216
  exact BoxTree.validC_splitK zoneCAssembly201_valid zoneCAssembly215_valid

def zoneCAssembly217 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2
    zoneCChunk198 zoneCAssembly216

theorem zoneCAssembly217_valid :
    zoneCAssembly217.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2 = true := by
  unfold zoneCAssembly217
  exact BoxTree.validC_splitE zoneCChunk198_valid zoneCAssembly216_valid

def zoneCAssembly218 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2
    zoneCAssembly192 zoneCAssembly217

theorem zoneCAssembly218_valid :
    zoneCAssembly218.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2 = true := by
  unfold zoneCAssembly218
  exact BoxTree.validC_splitK zoneCAssembly192_valid zoneCAssembly217_valid

def zoneCAssembly219 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2
    zoneCChunk192 zoneCAssembly218

theorem zoneCAssembly219_valid :
    zoneCAssembly219.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2 = true := by
  unfold zoneCAssembly219
  exact BoxTree.validC_splitE zoneCChunk192_valid zoneCAssembly218_valid

def zoneCAssembly220 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2
    zoneCChunk191 zoneCAssembly219

theorem zoneCAssembly220_valid :
    zoneCAssembly220.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2 = true := by
  unfold zoneCAssembly220
  exact BoxTree.validC_splitK zoneCChunk191_valid zoneCAssembly219_valid

def zoneCAssembly221 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1
    zoneCChunk190 zoneCAssembly220

theorem zoneCAssembly221_valid :
    zoneCAssembly221.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly221
  exact BoxTree.validC_splitK zoneCChunk190_valid zoneCAssembly220_valid

def zoneCAssembly222 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).1)).2)).1)).1)).2
    zoneCChunk229 zoneCChunk230

theorem zoneCAssembly222_valid :
    zoneCAssembly222.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).1)).2)).1)).1)).2 = true := by
  unfold zoneCAssembly222
  exact BoxTree.validC_splitK zoneCChunk229_valid zoneCChunk230_valid

def zoneCAssembly223 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).1)).2)).1)).1
    zoneCChunk228 zoneCAssembly222

theorem zoneCAssembly223_valid :
    zoneCAssembly223.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).1)).2)).1)).1 = true := by
  unfold zoneCAssembly223
  exact BoxTree.validC_splitE zoneCChunk228_valid zoneCAssembly222_valid

def zoneCAssembly224 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).1)).2)).1)).2)).2
    zoneCChunk232 zoneCChunk233

theorem zoneCAssembly224_valid :
    zoneCAssembly224.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).1)).2)).1)).2)).2 = true := by
  unfold zoneCAssembly224
  exact BoxTree.validC_splitK zoneCChunk232_valid zoneCChunk233_valid

def zoneCAssembly225 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).1)).2)).1)).2
    zoneCChunk231 zoneCAssembly224

theorem zoneCAssembly225_valid :
    zoneCAssembly225.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly225
  exact BoxTree.validC_splitE zoneCChunk231_valid zoneCAssembly224_valid

def zoneCAssembly226 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).1)).2)).1
    zoneCAssembly223 zoneCAssembly225

theorem zoneCAssembly226_valid :
    zoneCAssembly226.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).1)).2)).1 = true := by
  unfold zoneCAssembly226
  exact BoxTree.validC_splitK zoneCAssembly223_valid zoneCAssembly225_valid

def zoneCAssembly227 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).1)).2)).2)).2)).1
    zoneCChunk235 zoneCChunk236

theorem zoneCAssembly227_valid :
    zoneCAssembly227.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).1)).2)).2)).2)).1 = true := by
  unfold zoneCAssembly227
  exact BoxTree.validC_splitK zoneCChunk235_valid zoneCChunk236_valid

def zoneCAssembly228 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).1)).2)).2)).2
    zoneCAssembly227 zoneCChunk237

theorem zoneCAssembly228_valid :
    zoneCAssembly228.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).1)).2)).2)).2 = true := by
  unfold zoneCAssembly228
  exact BoxTree.validC_splitK zoneCAssembly227_valid zoneCChunk237_valid

def zoneCAssembly229 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).1)).2)).2
    zoneCChunk234 zoneCAssembly228

theorem zoneCAssembly229_valid :
    zoneCAssembly229.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).1)).2)).2 = true := by
  unfold zoneCAssembly229
  exact BoxTree.validC_splitE zoneCChunk234_valid zoneCAssembly228_valid

def zoneCAssembly230 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).1)).2
    zoneCAssembly226 zoneCAssembly229

theorem zoneCAssembly230_valid :
    zoneCAssembly230.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly230
  exact BoxTree.validC_splitK zoneCAssembly226_valid zoneCAssembly229_valid

def zoneCAssembly231 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).1
    zoneCChunk227 zoneCAssembly230

theorem zoneCAssembly231_valid :
    zoneCAssembly231.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).1 = true := by
  unfold zoneCAssembly231
  exact BoxTree.validC_splitE zoneCChunk227_valid zoneCAssembly230_valid

def zoneCAssembly232 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).2)).2)).1)).2
    zoneCChunk240 zoneCChunk241

theorem zoneCAssembly232_valid :
    zoneCAssembly232.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).2)).2)).1)).2 = true := by
  unfold zoneCAssembly232
  exact BoxTree.validC_splitK zoneCChunk240_valid zoneCChunk241_valid

def zoneCAssembly233 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).2)).2)).1
    zoneCChunk239 zoneCAssembly232

theorem zoneCAssembly233_valid :
    zoneCAssembly233.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).2)).2)).1 = true := by
  unfold zoneCAssembly233
  exact BoxTree.validC_splitE zoneCChunk239_valid zoneCAssembly232_valid

def zoneCAssembly234 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).2)).2)).2)).2
    zoneCChunk243 zoneCChunk244

theorem zoneCAssembly234_valid :
    zoneCAssembly234.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).2)).2)).2)).2 = true := by
  unfold zoneCAssembly234
  exact BoxTree.validC_splitK zoneCChunk243_valid zoneCChunk244_valid

def zoneCAssembly235 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).2)).2)).2
    zoneCChunk242 zoneCAssembly234

theorem zoneCAssembly235_valid :
    zoneCAssembly235.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).2)).2)).2 = true := by
  unfold zoneCAssembly235
  exact BoxTree.validC_splitE zoneCChunk242_valid zoneCAssembly234_valid

def zoneCAssembly236 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).2)).2
    zoneCAssembly233 zoneCAssembly235

theorem zoneCAssembly236_valid :
    zoneCAssembly236.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).2)).2 = true := by
  unfold zoneCAssembly236
  exact BoxTree.validC_splitK zoneCAssembly233_valid zoneCAssembly235_valid

def zoneCAssembly237 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).2
    zoneCChunk238 zoneCAssembly236

theorem zoneCAssembly237_valid :
    zoneCAssembly237.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).2 = true := by
  unfold zoneCAssembly237
  exact BoxTree.validC_splitE zoneCChunk238_valid zoneCAssembly236_valid

def zoneCAssembly238 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2
    zoneCAssembly231 zoneCAssembly237

theorem zoneCAssembly238_valid :
    zoneCAssembly238.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly238
  exact BoxTree.validC_splitK zoneCAssembly231_valid zoneCAssembly237_valid

def zoneCAssembly239 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1
    zoneCChunk226 zoneCAssembly238

theorem zoneCAssembly239_valid :
    zoneCAssembly239.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1 = true := by
  unfold zoneCAssembly239
  exact BoxTree.validC_splitE zoneCChunk226_valid zoneCAssembly238_valid

def zoneCAssembly240 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2)).1)).2)).1)).2
    zoneCChunk248 zoneCChunk249

theorem zoneCAssembly240_valid :
    zoneCAssembly240.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly240
  exact BoxTree.validC_splitK zoneCChunk248_valid zoneCChunk249_valid

def zoneCAssembly241 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2)).1)).2)).1
    zoneCChunk247 zoneCAssembly240

theorem zoneCAssembly241_valid :
    zoneCAssembly241.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2)).1)).2)).1 = true := by
  unfold zoneCAssembly241
  exact BoxTree.validC_splitE zoneCChunk247_valid zoneCAssembly240_valid

def zoneCAssembly242 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2)).1)).2)).2)).2
    zoneCChunk251 zoneCChunk252

theorem zoneCAssembly242_valid :
    zoneCAssembly242.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2)).1)).2)).2)).2 = true := by
  unfold zoneCAssembly242
  exact BoxTree.validC_splitK zoneCChunk251_valid zoneCChunk252_valid

def zoneCAssembly243 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2)).1)).2)).2
    zoneCChunk250 zoneCAssembly242

theorem zoneCAssembly243_valid :
    zoneCAssembly243.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2)).1)).2)).2 = true := by
  unfold zoneCAssembly243
  exact BoxTree.validC_splitE zoneCChunk250_valid zoneCAssembly242_valid

def zoneCAssembly244 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2)).1)).2
    zoneCAssembly241 zoneCAssembly243

theorem zoneCAssembly244_valid :
    zoneCAssembly244.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2)).1)).2 = true := by
  unfold zoneCAssembly244
  exact BoxTree.validC_splitK zoneCAssembly241_valid zoneCAssembly243_valid

def zoneCAssembly245 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2)).1
    zoneCChunk246 zoneCAssembly244

theorem zoneCAssembly245_valid :
    zoneCAssembly245.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2)).1 = true := by
  unfold zoneCAssembly245
  exact BoxTree.validC_splitE zoneCChunk246_valid zoneCAssembly244_valid

def zoneCAssembly246 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2)).2)).2)).1)).2
    zoneCChunk255 zoneCChunk256

theorem zoneCAssembly246_valid :
    zoneCAssembly246.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2)).2)).2)).1)).2 = true := by
  unfold zoneCAssembly246
  exact BoxTree.validC_splitK zoneCChunk255_valid zoneCChunk256_valid

def zoneCAssembly247 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2)).2)).2)).1
    zoneCChunk254 zoneCAssembly246

theorem zoneCAssembly247_valid :
    zoneCAssembly247.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2)).2)).2)).1 = true := by
  unfold zoneCAssembly247
  exact BoxTree.validC_splitE zoneCChunk254_valid zoneCAssembly246_valid

def zoneCAssembly248 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2)).2)).2)).2)).2
    zoneCChunk258 zoneCChunk259

theorem zoneCAssembly248_valid :
    zoneCAssembly248.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2)).2)).2)).2)).2 = true := by
  unfold zoneCAssembly248
  exact BoxTree.validC_splitK zoneCChunk258_valid zoneCChunk259_valid

def zoneCAssembly249 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2)).2)).2)).2
    zoneCChunk257 zoneCAssembly248

theorem zoneCAssembly249_valid :
    zoneCAssembly249.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2)).2)).2)).2 = true := by
  unfold zoneCAssembly249
  exact BoxTree.validC_splitE zoneCChunk257_valid zoneCAssembly248_valid

def zoneCAssembly250 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2)).2)).2
    zoneCAssembly247 zoneCAssembly249

theorem zoneCAssembly250_valid :
    zoneCAssembly250.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2)).2)).2 = true := by
  unfold zoneCAssembly250
  exact BoxTree.validC_splitK zoneCAssembly247_valid zoneCAssembly249_valid

def zoneCAssembly251 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2)).2
    zoneCChunk253 zoneCAssembly250

theorem zoneCAssembly251_valid :
    zoneCAssembly251.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2)).2 = true := by
  unfold zoneCAssembly251
  exact BoxTree.validC_splitE zoneCChunk253_valid zoneCAssembly250_valid

def zoneCAssembly252 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2
    zoneCAssembly245 zoneCAssembly251

theorem zoneCAssembly252_valid :
    zoneCAssembly252.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2 = true := by
  unfold zoneCAssembly252
  exact BoxTree.validC_splitK zoneCAssembly245_valid zoneCAssembly251_valid

def zoneCAssembly253 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2
    zoneCChunk245 zoneCAssembly252

theorem zoneCAssembly253_valid :
    zoneCAssembly253.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2 = true := by
  unfold zoneCAssembly253
  exact BoxTree.validC_splitE zoneCChunk245_valid zoneCAssembly252_valid

def zoneCAssembly254 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2
    zoneCAssembly239 zoneCAssembly253

theorem zoneCAssembly254_valid :
    zoneCAssembly254.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly254
  exact BoxTree.validC_splitK zoneCAssembly239_valid zoneCAssembly253_valid

def zoneCAssembly255 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1
    zoneCChunk225 zoneCAssembly254

theorem zoneCAssembly255_valid :
    zoneCAssembly255.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1 = true := by
  unfold zoneCAssembly255
  exact BoxTree.validC_splitE zoneCChunk225_valid zoneCAssembly254_valid

def zoneCAssembly256 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).2)).1)).2)).1)).2
    zoneCChunk264 zoneCChunk265

theorem zoneCAssembly256_valid :
    zoneCAssembly256.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).2)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly256
  exact BoxTree.validC_splitK zoneCChunk264_valid zoneCChunk265_valid

def zoneCAssembly257 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).2)).1)).2)).1
    zoneCChunk263 zoneCAssembly256

theorem zoneCAssembly257_valid :
    zoneCAssembly257.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).2)).1)).2)).1 = true := by
  unfold zoneCAssembly257
  exact BoxTree.validC_splitE zoneCChunk263_valid zoneCAssembly256_valid

def zoneCAssembly258 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).2)).1)).2)).2)).2
    zoneCChunk267 zoneCChunk268

theorem zoneCAssembly258_valid :
    zoneCAssembly258.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).2)).1)).2)).2)).2 = true := by
  unfold zoneCAssembly258
  exact BoxTree.validC_splitK zoneCChunk267_valid zoneCChunk268_valid

def zoneCAssembly259 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).2)).1)).2)).2
    zoneCChunk266 zoneCAssembly258

theorem zoneCAssembly259_valid :
    zoneCAssembly259.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).2)).1)).2)).2 = true := by
  unfold zoneCAssembly259
  exact BoxTree.validC_splitE zoneCChunk266_valid zoneCAssembly258_valid

def zoneCAssembly260 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).2)).1)).2
    zoneCAssembly257 zoneCAssembly259

theorem zoneCAssembly260_valid :
    zoneCAssembly260.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly260
  exact BoxTree.validC_splitK zoneCAssembly257_valid zoneCAssembly259_valid

def zoneCAssembly261 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).2)).1
    zoneCChunk262 zoneCAssembly260

theorem zoneCAssembly261_valid :
    zoneCAssembly261.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).2)).1 = true := by
  unfold zoneCAssembly261
  exact BoxTree.validC_splitE zoneCChunk262_valid zoneCAssembly260_valid

def zoneCAssembly262 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).2)).2)).2)).1)).2
    zoneCChunk271 zoneCChunk272

theorem zoneCAssembly262_valid :
    zoneCAssembly262.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).2)).2)).2)).1)).2 = true := by
  unfold zoneCAssembly262
  exact BoxTree.validC_splitK zoneCChunk271_valid zoneCChunk272_valid

def zoneCAssembly263 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).2)).2)).2)).1
    zoneCChunk270 zoneCAssembly262

theorem zoneCAssembly263_valid :
    zoneCAssembly263.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).2)).2)).2)).1 = true := by
  unfold zoneCAssembly263
  exact BoxTree.validC_splitE zoneCChunk270_valid zoneCAssembly262_valid

def zoneCAssembly264 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).2)).2)).2)).2)).2
    zoneCChunk274 zoneCChunk275

theorem zoneCAssembly264_valid :
    zoneCAssembly264.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).2)).2)).2)).2)).2 = true := by
  unfold zoneCAssembly264
  exact BoxTree.validC_splitK zoneCChunk274_valid zoneCChunk275_valid

def zoneCAssembly265 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).2)).2)).2)).2
    zoneCChunk273 zoneCAssembly264

theorem zoneCAssembly265_valid :
    zoneCAssembly265.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).2)).2)).2)).2 = true := by
  unfold zoneCAssembly265
  exact BoxTree.validC_splitE zoneCChunk273_valid zoneCAssembly264_valid

def zoneCAssembly266 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).2)).2)).2
    zoneCAssembly263 zoneCAssembly265

theorem zoneCAssembly266_valid :
    zoneCAssembly266.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).2)).2)).2 = true := by
  unfold zoneCAssembly266
  exact BoxTree.validC_splitK zoneCAssembly263_valid zoneCAssembly265_valid

def zoneCAssembly267 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).2)).2
    zoneCChunk269 zoneCAssembly266

theorem zoneCAssembly267_valid :
    zoneCAssembly267.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).2)).2 = true := by
  unfold zoneCAssembly267
  exact BoxTree.validC_splitE zoneCChunk269_valid zoneCAssembly266_valid

def zoneCAssembly268 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).2
    zoneCAssembly261 zoneCAssembly267

theorem zoneCAssembly268_valid :
    zoneCAssembly268.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1)).2 = true := by
  unfold zoneCAssembly268
  exact BoxTree.validC_splitK zoneCAssembly261_valid zoneCAssembly267_valid

def zoneCAssembly269 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1
    zoneCChunk261 zoneCAssembly268

theorem zoneCAssembly269_valid :
    zoneCAssembly269.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).1 = true := by
  unfold zoneCAssembly269
  exact BoxTree.validC_splitE zoneCChunk261_valid zoneCAssembly268_valid

def zoneCAssembly270 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).2)).2)).1)).2)).1)).2
    zoneCChunk279 zoneCChunk280

theorem zoneCAssembly270_valid :
    zoneCAssembly270.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).2)).2)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly270
  exact BoxTree.validC_splitK zoneCChunk279_valid zoneCChunk280_valid

def zoneCAssembly271 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).2)).2)).1)).2)).1
    zoneCChunk278 zoneCAssembly270

theorem zoneCAssembly271_valid :
    zoneCAssembly271.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).2)).2)).1)).2)).1 = true := by
  unfold zoneCAssembly271
  exact BoxTree.validC_splitE zoneCChunk278_valid zoneCAssembly270_valid

def zoneCAssembly272 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).2)).2)).1)).2
    zoneCAssembly271 zoneCChunk281

theorem zoneCAssembly272_valid :
    zoneCAssembly272.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).2)).2)).1)).2 = true := by
  unfold zoneCAssembly272
  exact BoxTree.validC_splitK zoneCAssembly271_valid zoneCChunk281_valid

def zoneCAssembly273 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).2)).2)).1
    zoneCChunk277 zoneCAssembly272

theorem zoneCAssembly273_valid :
    zoneCAssembly273.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).2)).2)).1 = true := by
  unfold zoneCAssembly273
  exact BoxTree.validC_splitE zoneCChunk277_valid zoneCAssembly272_valid

def zoneCAssembly274 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).2)).2)).2)).2
    zoneCChunk283 zoneCChunk284

theorem zoneCAssembly274_valid :
    zoneCAssembly274.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).2)).2)).2)).2 = true := by
  unfold zoneCAssembly274
  exact BoxTree.validC_splitK zoneCChunk283_valid zoneCChunk284_valid

def zoneCAssembly275 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).2)).2)).2
    zoneCChunk282 zoneCAssembly274

theorem zoneCAssembly275_valid :
    zoneCAssembly275.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).2)).2)).2 = true := by
  unfold zoneCAssembly275
  exact BoxTree.validC_splitE zoneCChunk282_valid zoneCAssembly274_valid

def zoneCAssembly276 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).2)).2
    zoneCAssembly273 zoneCAssembly275

theorem zoneCAssembly276_valid :
    zoneCAssembly276.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).2)).2 = true := by
  unfold zoneCAssembly276
  exact BoxTree.validC_splitK zoneCAssembly273_valid zoneCAssembly275_valid

def zoneCAssembly277 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).2
    zoneCChunk276 zoneCAssembly276

theorem zoneCAssembly277_valid :
    zoneCAssembly277.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2)).2 = true := by
  unfold zoneCAssembly277
  exact BoxTree.validC_splitE zoneCChunk276_valid zoneCAssembly276_valid

def zoneCAssembly278 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2
    zoneCAssembly269 zoneCAssembly277

theorem zoneCAssembly278_valid :
    zoneCAssembly278.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2 = true := by
  unfold zoneCAssembly278
  exact BoxTree.validC_splitK zoneCAssembly269_valid zoneCAssembly277_valid

def zoneCAssembly279 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2
    zoneCChunk260 zoneCAssembly278

theorem zoneCAssembly279_valid :
    zoneCAssembly279.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2 = true := by
  unfold zoneCAssembly279
  exact BoxTree.validC_splitE zoneCChunk260_valid zoneCAssembly278_valid

def zoneCAssembly280 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2
    zoneCAssembly255 zoneCAssembly279

theorem zoneCAssembly280_valid :
    zoneCAssembly280.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly280
  exact BoxTree.validC_splitK zoneCAssembly255_valid zoneCAssembly279_valid

def zoneCAssembly281 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1
    zoneCChunk224 zoneCAssembly280

theorem zoneCAssembly281_valid :
    zoneCAssembly281.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1 = true := by
  unfold zoneCAssembly281
  exact BoxTree.validC_splitE zoneCChunk224_valid zoneCAssembly280_valid

def zoneCAssembly282 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2)).1)).2)).1)).2
    zoneCChunk289 zoneCChunk290

theorem zoneCAssembly282_valid :
    zoneCAssembly282.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly282
  exact BoxTree.validC_splitK zoneCChunk289_valid zoneCChunk290_valid

def zoneCAssembly283 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2)).1)).2)).1
    zoneCChunk288 zoneCAssembly282

theorem zoneCAssembly283_valid :
    zoneCAssembly283.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2)).1)).2)).1 = true := by
  unfold zoneCAssembly283
  exact BoxTree.validC_splitE zoneCChunk288_valid zoneCAssembly282_valid

def zoneCAssembly284 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2)).1)).2)).2)).2
    zoneCChunk292 zoneCChunk293

theorem zoneCAssembly284_valid :
    zoneCAssembly284.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2)).1)).2)).2)).2 = true := by
  unfold zoneCAssembly284
  exact BoxTree.validC_splitK zoneCChunk292_valid zoneCChunk293_valid

def zoneCAssembly285 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2)).1)).2)).2
    zoneCChunk291 zoneCAssembly284

theorem zoneCAssembly285_valid :
    zoneCAssembly285.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2)).1)).2)).2 = true := by
  unfold zoneCAssembly285
  exact BoxTree.validC_splitE zoneCChunk291_valid zoneCAssembly284_valid

def zoneCAssembly286 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2)).1)).2
    zoneCAssembly283 zoneCAssembly285

theorem zoneCAssembly286_valid :
    zoneCAssembly286.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly286
  exact BoxTree.validC_splitK zoneCAssembly283_valid zoneCAssembly285_valid

def zoneCAssembly287 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2)).1
    zoneCChunk287 zoneCAssembly286

theorem zoneCAssembly287_valid :
    zoneCAssembly287.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2)).1 = true := by
  unfold zoneCAssembly287
  exact BoxTree.validC_splitE zoneCChunk287_valid zoneCAssembly286_valid

def zoneCAssembly288 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2)).2)).2)).1)).2
    zoneCChunk296 zoneCChunk297

theorem zoneCAssembly288_valid :
    zoneCAssembly288.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2)).2)).2)).1)).2 = true := by
  unfold zoneCAssembly288
  exact BoxTree.validC_splitK zoneCChunk296_valid zoneCChunk297_valid

def zoneCAssembly289 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2)).2)).2)).1
    zoneCChunk295 zoneCAssembly288

theorem zoneCAssembly289_valid :
    zoneCAssembly289.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2)).2)).2)).1 = true := by
  unfold zoneCAssembly289
  exact BoxTree.validC_splitE zoneCChunk295_valid zoneCAssembly288_valid

def zoneCAssembly290 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2)).2)).2)).2)).2
    zoneCChunk299 zoneCChunk300

theorem zoneCAssembly290_valid :
    zoneCAssembly290.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2)).2)).2)).2)).2 = true := by
  unfold zoneCAssembly290
  exact BoxTree.validC_splitK zoneCChunk299_valid zoneCChunk300_valid

def zoneCAssembly291 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2)).2)).2)).2
    zoneCChunk298 zoneCAssembly290

theorem zoneCAssembly291_valid :
    zoneCAssembly291.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2)).2)).2)).2 = true := by
  unfold zoneCAssembly291
  exact BoxTree.validC_splitE zoneCChunk298_valid zoneCAssembly290_valid

def zoneCAssembly292 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2)).2)).2
    zoneCAssembly289 zoneCAssembly291

theorem zoneCAssembly292_valid :
    zoneCAssembly292.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2)).2)).2 = true := by
  unfold zoneCAssembly292
  exact BoxTree.validC_splitK zoneCAssembly289_valid zoneCAssembly291_valid

def zoneCAssembly293 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2)).2
    zoneCChunk294 zoneCAssembly292

theorem zoneCAssembly293_valid :
    zoneCAssembly293.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2)).2 = true := by
  unfold zoneCAssembly293
  exact BoxTree.validC_splitE zoneCChunk294_valid zoneCAssembly292_valid

def zoneCAssembly294 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2
    zoneCAssembly287 zoneCAssembly293

theorem zoneCAssembly294_valid :
    zoneCAssembly294.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2 = true := by
  unfold zoneCAssembly294
  exact BoxTree.validC_splitK zoneCAssembly287_valid zoneCAssembly293_valid

def zoneCAssembly295 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1
    zoneCChunk286 zoneCAssembly294

theorem zoneCAssembly295_valid :
    zoneCAssembly295.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1 = true := by
  unfold zoneCAssembly295
  exact BoxTree.validC_splitE zoneCChunk286_valid zoneCAssembly294_valid

def zoneCAssembly296 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1)).2)).1)).2
    zoneCChunk304 zoneCChunk305

theorem zoneCAssembly296_valid :
    zoneCAssembly296.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly296
  exact BoxTree.validC_splitK zoneCChunk304_valid zoneCChunk305_valid

def zoneCAssembly297 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1)).2)).1
    zoneCChunk303 zoneCAssembly296

theorem zoneCAssembly297_valid :
    zoneCAssembly297.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1)).2)).1 = true := by
  unfold zoneCAssembly297
  exact BoxTree.validC_splitE zoneCChunk303_valid zoneCAssembly296_valid

def zoneCAssembly298 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1)).2)).2)).2
    zoneCChunk307 zoneCChunk308

theorem zoneCAssembly298_valid :
    zoneCAssembly298.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1)).2)).2)).2 = true := by
  unfold zoneCAssembly298
  exact BoxTree.validC_splitK zoneCChunk307_valid zoneCChunk308_valid

def zoneCAssembly299 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1)).2)).2
    zoneCChunk306 zoneCAssembly298

theorem zoneCAssembly299_valid :
    zoneCAssembly299.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1)).2)).2 = true := by
  unfold zoneCAssembly299
  exact BoxTree.validC_splitE zoneCChunk306_valid zoneCAssembly298_valid

def zoneCAssembly300 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1)).2
    zoneCAssembly297 zoneCAssembly299

theorem zoneCAssembly300_valid :
    zoneCAssembly300.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1)).2 = true := by
  unfold zoneCAssembly300
  exact BoxTree.validC_splitK zoneCAssembly297_valid zoneCAssembly299_valid

def zoneCAssembly301 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1
    zoneCChunk302 zoneCAssembly300

theorem zoneCAssembly301_valid :
    zoneCAssembly301.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).1 = true := by
  unfold zoneCAssembly301
  exact BoxTree.validC_splitE zoneCChunk302_valid zoneCAssembly300_valid

def zoneCAssembly302 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2)).2
    zoneCChunk310 zoneCChunk311

theorem zoneCAssembly302_valid :
    zoneCAssembly302.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2)).2 = true := by
  unfold zoneCAssembly302
  exact BoxTree.validC_splitK zoneCChunk310_valid zoneCChunk311_valid

def zoneCAssembly303 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2
    zoneCChunk309 zoneCAssembly302

theorem zoneCAssembly303_valid :
    zoneCAssembly303.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2)).2 = true := by
  unfold zoneCAssembly303
  exact BoxTree.validC_splitE zoneCChunk309_valid zoneCAssembly302_valid

def zoneCAssembly304 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2
    zoneCAssembly301 zoneCAssembly303

theorem zoneCAssembly304_valid :
    zoneCAssembly304.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2)).2 = true := by
  unfold zoneCAssembly304
  exact BoxTree.validC_splitK zoneCAssembly301_valid zoneCAssembly303_valid

def zoneCAssembly305 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2
    zoneCChunk301 zoneCAssembly304

theorem zoneCAssembly305_valid :
    zoneCAssembly305.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).2 = true := by
  unfold zoneCAssembly305
  exact BoxTree.validC_splitE zoneCChunk301_valid zoneCAssembly304_valid

def zoneCAssembly306 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2
    zoneCAssembly295 zoneCAssembly305

theorem zoneCAssembly306_valid :
    zoneCAssembly306.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2 = true := by
  unfold zoneCAssembly306
  exact BoxTree.validC_splitK zoneCAssembly295_valid zoneCAssembly305_valid

def zoneCAssembly307 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2
    zoneCChunk285 zoneCAssembly306

theorem zoneCAssembly307_valid :
    zoneCAssembly307.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2 = true := by
  unfold zoneCAssembly307
  exact BoxTree.validC_splitE zoneCChunk285_valid zoneCAssembly306_valid

def zoneCAssembly308 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2
    zoneCAssembly281 zoneCAssembly307

theorem zoneCAssembly308_valid :
    zoneCAssembly308.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1)).2 = true := by
  unfold zoneCAssembly308
  exact BoxTree.validC_splitK zoneCAssembly281_valid zoneCAssembly307_valid

def zoneCAssembly309 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1
    zoneCAssembly221 zoneCAssembly308

theorem zoneCAssembly309_valid :
    zoneCAssembly309.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly309
  exact BoxTree.validC_splitK zoneCAssembly221_valid zoneCAssembly308_valid

def zoneCAssembly310 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).1)).2
    zoneCChunk316 zoneCChunk317

theorem zoneCAssembly310_valid :
    zoneCAssembly310.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly310
  exact BoxTree.validC_splitK zoneCChunk316_valid zoneCChunk317_valid

def zoneCAssembly311 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).1
    zoneCChunk315 zoneCAssembly310

theorem zoneCAssembly311_valid :
    zoneCAssembly311.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2)).1 = true := by
  unfold zoneCAssembly311
  exact BoxTree.validC_splitE zoneCChunk315_valid zoneCAssembly310_valid

def zoneCAssembly312 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2
    zoneCAssembly311 zoneCChunk318

theorem zoneCAssembly312_valid :
    zoneCAssembly312.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly312
  exact BoxTree.validC_splitK zoneCAssembly311_valid zoneCChunk318_valid

def zoneCAssembly313 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1
    zoneCChunk314 zoneCAssembly312

theorem zoneCAssembly313_valid :
    zoneCAssembly313.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).1 = true := by
  unfold zoneCAssembly313
  exact BoxTree.validC_splitE zoneCChunk314_valid zoneCAssembly312_valid

def zoneCAssembly314 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2
    zoneCChunk320 zoneCChunk321

theorem zoneCAssembly314_valid :
    zoneCAssembly314.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2)).2 = true := by
  unfold zoneCAssembly314
  exact BoxTree.validC_splitK zoneCChunk320_valid zoneCChunk321_valid

def zoneCAssembly315 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2
    zoneCChunk319 zoneCAssembly314

theorem zoneCAssembly315_valid :
    zoneCAssembly315.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2)).2 = true := by
  unfold zoneCAssembly315
  exact BoxTree.validC_splitE zoneCChunk319_valid zoneCAssembly314_valid

def zoneCAssembly316 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2
    zoneCAssembly313 zoneCAssembly315

theorem zoneCAssembly316_valid :
    zoneCAssembly316.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly316
  exact BoxTree.validC_splitK zoneCAssembly313_valid zoneCAssembly315_valid

def zoneCAssembly317 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1
    zoneCChunk313 zoneCAssembly316

theorem zoneCAssembly317_valid :
    zoneCAssembly317.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).1 = true := by
  unfold zoneCAssembly317
  exact BoxTree.validC_splitE zoneCChunk313_valid zoneCAssembly316_valid

def zoneCAssembly318 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2
    zoneCChunk323 zoneCChunk324

theorem zoneCAssembly318_valid :
    zoneCAssembly318.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2)).2 = true := by
  unfold zoneCAssembly318
  exact BoxTree.validC_splitK zoneCChunk323_valid zoneCChunk324_valid

def zoneCAssembly319 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2
    zoneCChunk322 zoneCAssembly318

theorem zoneCAssembly319_valid :
    zoneCAssembly319.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2)).2 = true := by
  unfold zoneCAssembly319
  exact BoxTree.validC_splitE zoneCChunk322_valid zoneCAssembly318_valid

def zoneCAssembly320 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2
    zoneCAssembly317 zoneCAssembly319

theorem zoneCAssembly320_valid :
    zoneCAssembly320.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly320
  exact BoxTree.validC_splitK zoneCAssembly317_valid zoneCAssembly319_valid

def zoneCAssembly321 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1
    zoneCChunk312 zoneCAssembly320

theorem zoneCAssembly321_valid :
    zoneCAssembly321.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).1 = true := by
  unfold zoneCAssembly321
  exact BoxTree.validC_splitE zoneCChunk312_valid zoneCAssembly320_valid

def zoneCAssembly322 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2
    zoneCChunk327 zoneCChunk328

theorem zoneCAssembly322_valid :
    zoneCAssembly322.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1)).2 = true := by
  unfold zoneCAssembly322
  exact BoxTree.validC_splitK zoneCChunk327_valid zoneCChunk328_valid

def zoneCAssembly323 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1
    zoneCChunk326 zoneCAssembly322

theorem zoneCAssembly323_valid :
    zoneCAssembly323.validC (RatBox.splitK ((RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2)).1 = true := by
  unfold zoneCAssembly323
  exact BoxTree.validC_splitE zoneCChunk326_valid zoneCAssembly322_valid

def zoneCAssembly324 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2
    zoneCAssembly323 zoneCChunk329

theorem zoneCAssembly324_valid :
    zoneCAssembly324.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2)).2 = true := by
  unfold zoneCAssembly324
  exact BoxTree.validC_splitK zoneCAssembly323_valid zoneCChunk329_valid

def zoneCAssembly325 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2
    zoneCChunk325 zoneCAssembly324

theorem zoneCAssembly325_valid :
    zoneCAssembly325.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2)).2 = true := by
  unfold zoneCAssembly325
  exact BoxTree.validC_splitE zoneCChunk325_valid zoneCAssembly324_valid

def zoneCAssembly326 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2
    zoneCAssembly321 zoneCAssembly325

theorem zoneCAssembly326_valid :
    zoneCAssembly326.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1)).2 = true := by
  unfold zoneCAssembly326
  exact BoxTree.validC_splitK zoneCAssembly321_valid zoneCAssembly325_valid

def zoneCAssembly327 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1
    zoneCAssembly309 zoneCAssembly326

theorem zoneCAssembly327_valid :
    zoneCAssembly327.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly327
  exact BoxTree.validC_splitK zoneCAssembly309_valid zoneCAssembly326_valid

def zoneCAssembly328 : BoxTree :=
  .splitK (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2
    zoneCChunk331 zoneCChunk332

theorem zoneCAssembly328_valid :
    zoneCAssembly328.validC (RatBox.splitE ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).2)).1)).2 = true := by
  unfold zoneCAssembly328
  exact BoxTree.validC_splitK zoneCChunk331_valid zoneCChunk332_valid

def zoneCAssembly329 : BoxTree :=
  .splitE (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).2)).1
    zoneCChunk330 zoneCAssembly328

theorem zoneCAssembly329_valid :
    zoneCAssembly329.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).2)).1 = true := by
  unfold zoneCAssembly329
  exact BoxTree.validC_splitE zoneCChunk330_valid zoneCAssembly328_valid

def zoneCAssembly330 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).2
    zoneCAssembly329 zoneCChunk333

theorem zoneCAssembly330_valid :
    zoneCAssembly330.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1)).2 = true := by
  unfold zoneCAssembly330
  exact BoxTree.validC_splitK zoneCAssembly329_valid zoneCChunk333_valid

def zoneCAssembly331 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1
    zoneCAssembly327 zoneCAssembly330

theorem zoneCAssembly331_valid :
    zoneCAssembly331.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly331
  exact BoxTree.validC_splitK zoneCAssembly327_valid zoneCAssembly330_valid

def zoneCAssembly332 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1
    zoneCAssembly331 zoneCChunk334

theorem zoneCAssembly332_valid :
    zoneCAssembly332.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly332
  exact BoxTree.validC_splitK zoneCAssembly331_valid zoneCChunk334_valid

def zoneCAssembly333 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1
    zoneCAssembly332 zoneCChunk335

theorem zoneCAssembly333_valid :
    zoneCAssembly333.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly333
  exact BoxTree.validC_splitK zoneCAssembly332_valid zoneCChunk335_valid

def zoneCAssembly334 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1
    zoneCAssembly333 zoneCChunk336

theorem zoneCAssembly334_valid :
    zoneCAssembly334.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1)).1 = true := by
  unfold zoneCAssembly334
  exact BoxTree.validC_splitK zoneCAssembly333_valid zoneCChunk336_valid

def zoneCAssembly335 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1
    zoneCAssembly334 zoneCChunk337

theorem zoneCAssembly335_valid :
    zoneCAssembly335.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1)).1 = true := by
  unfold zoneCAssembly335
  exact BoxTree.validC_splitK zoneCAssembly334_valid zoneCChunk337_valid

def zoneCAssembly336 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1
    zoneCAssembly335 zoneCChunk338

theorem zoneCAssembly336_valid :
    zoneCAssembly336.validC (RatBox.splitK ((RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1)).1 = true := by
  unfold zoneCAssembly336
  exact BoxTree.validC_splitK zoneCAssembly335_valid zoneCChunk338_valid

def zoneCAssembly337 : BoxTree :=
  .splitK (RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1
    zoneCAssembly336 zoneCChunk339

theorem zoneCAssembly337_valid :
    zoneCAssembly337.validC (RatBox.splitK ((RatBox.splitE (zoneCRoot)).2)).1 = true := by
  unfold zoneCAssembly337
  exact BoxTree.validC_splitK zoneCAssembly336_valid zoneCChunk339_valid

def zoneCAssembly338 : BoxTree :=
  .splitK (RatBox.splitE (zoneCRoot)).2
    zoneCAssembly337 zoneCChunk340

theorem zoneCAssembly338_valid :
    zoneCAssembly338.validC (RatBox.splitE (zoneCRoot)).2 = true := by
  unfold zoneCAssembly338
  exact BoxTree.validC_splitK zoneCAssembly337_valid zoneCChunk340_valid

def zoneCAssembly339 : BoxTree :=
  .splitE zoneCRoot
    zoneCAssembly188 zoneCAssembly338

theorem zoneCAssembly339_valid :
    zoneCAssembly339.validC zoneCRoot = true := by
  unfold zoneCAssembly339
  exact BoxTree.validC_splitE zoneCAssembly188_valid zoneCAssembly338_valid

def zoneCChunkedTree : BoxTree :=
  zoneCAssembly339

theorem zoneC_chunkedTree_valid :
    zoneCChunkedTree.validC zoneCRoot = true := by
  simpa only [zoneCChunkedTree] using zoneCAssembly339_valid

end OddCycleBound.RegionII.Certificate
