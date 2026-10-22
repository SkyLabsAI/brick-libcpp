<template>
  <div class="page-number"><SlideCurrentNo /> / <SlidesTotal /></div>
</template>

<style scoped>
.page-number {
  position: absolute;
  right: 48px;
  bottom: 26px;
  z-index: 10;
  color: #637079;
  font-family: Arial, sans-serif;
  font-size: 20px;
  font-variant-numeric: tabular-nums;
  line-height: 1.3;
  pointer-events: none;
}
</style>
