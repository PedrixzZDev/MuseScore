/*
 * SPDX-License-Identifier: GPL-3.0-only
 * MuseScore-Studio-CLA-applies
 *
 * MuseScore Studio
 * Music Composition & Notation
 *
 * Copyright (C) 2025 MuseScore Limited
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License version 3 as
 * published by the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */
#pragma once

#include <types/fraction.h>

namespace mu::engraving {
class Note;
class Chord;
}

namespace mu::iex::guitarpro {
struct BendNoteData {
    double startFactor = 0.0;
    double endFactor = 1.0;
    int quarterTones = 0;
};

using bend_data_map_t       = std::map<size_t /* idx in chord */, BendNoteData>;
using grace_bend_data_map_t = std::map<size_t /* idx in chord */, std::vector<BendNoteData> >; // each note can have multiple grace notes connected

struct BendChordData {
    mu::engraving::Fraction startTick;
    bend_data_map_t noteDataByIdx;
};

struct BendSegment {
    int startTime = -1;
    int middleTime = -1;
    int endTime = -1;
    int startPitch = -1;
    int endPitch = -1;

    int pitchDiff() const { return endPitch - startPitch; }
};

enum class BendType {
    NORMAL_BEND,
    PREBEND,
    TIED_TO_PREVIOUS_NOTE,
    SLIGHT_BEND
};

struct ImportedBendInfo {
    const mu::engraving::Note* note = nullptr;
    std::vector<BendSegment> segments;
    BendType type = BendType::NORMAL_BEND;
    int timeOffsetFromStart = 0;
    int pitchOffsetFromStart = 0;
    bool connectsToNextNote = false;

    bool isSlightBend() const { return type == BendType::SLIGHT_BEND; }
    bool startsWithPrebend() const { return type == BendType::PREBEND; }
};

struct ChordImportedBendData {
    mu::engraving::Chord* chord = nullptr;
    std::map<mu::engraving::Note*, ImportedBendInfo> dataByNote;
};

struct TiedChordsBendDataChunk {
    std::vector<ChordImportedBendData> chordsData;
    bool shouldConnectToNext = false;
};
} // mu::iex::guitarpro
