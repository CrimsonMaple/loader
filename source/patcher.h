#pragma once

#include <3ds/types.h>

void initPatcher(void);
void exitPatcher(void);
int patch_code(u64 progid, u16 progVer, u32 textSize, u8 *code, u32 size);
