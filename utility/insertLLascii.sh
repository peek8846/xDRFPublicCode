#!/bin/bash

sed -i 's/^\(.*!resndrf7.*\)$/  call void asm sideeffect ".ascii\\09\\22begin_resndrf 7\\22", "~{edi}"()\n\1\n  call void asm sideeffect ".ascii\\09\\22end_resndrf 7\\22", "~{edi}"()/' "$1"
sed -i 's/^\(.*!resndrf8.*\)$/  call void asm sideeffect ".ascii\\09\\22begin_resndrf 8\\22", "~{edi}"()\n\1\n  call void asm sideeffect ".ascii\\09\\22end_resndrf 8\\22", "~{edi}"()/' "$1"
sed -i 's/^\(.*!resndrf9.*\)$/  call void asm sideeffect ".ascii\\09\\22begin_resndrf 9\\22", "~{edi}"()\n\1\n  call void asm sideeffect ".ascii\\09\\22end_resndrf 9\\22", "~{edi}"()/' "$1"
sed -i 's/^\(.*!resndrf10.*\)$/  call void asm sideeffect ".ascii\\09\\22begin_resndrf 10\\22", "~{edi}"()\n\1\n  call void asm sideeffect ".ascii\\09\\22end_resndrf 10\\22", "~{edi}"()/' "$1"
sed -i 's/^\(.*!resndrf11.*\)$/  call void asm sideeffect ".ascii\\09\\22begin_resndrf 11\\22", "~{edi}"()\n\1\n  call void asm sideeffect ".ascii\\09\\22end_resndrf 11\\22", "~{edi}"()/' "$1"
sed -i 's/^\(.*!resndrf12.*\)$/  call void asm sideeffect ".ascii\\09\\22begin_resndrf 12\\22", "~{edi}"()\n\1\n  call void asm sideeffect ".ascii\\09\\22end_resndrf 12\\22", "~{edi}"()/' "$1"
