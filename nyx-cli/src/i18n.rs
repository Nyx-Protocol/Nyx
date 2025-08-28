//! Minimal i18n table_s for CLI message_s (EN/JA) with safe fallback.

#![forbid(unsafe_code)]

use std::collection_s::HashMap;

pub type I18nTable = HashMap<&'static str, &'static str>;

fn base_en() -> I18nTable {
	// Keep key_s stable and short; value_s are static &'static str
	let pair_s: [(&str, &str); 16] = [
		("app.title", "Nyx CLI"),
		("app.version", "Version"),
		("app.error", "Error"),
		("cmd.connect", "Connect to daemon"),
		("cmd.disconnect", "Disconnect"),
		("cmd.statu_s", "Show statu_s"),
		("cmd.config", "Manage configuration"),
		("cmd.config.reload", "Reload configuration"),
		("cmd.config.update", "Update configuration"),
		("cmd.event_s", "Subscribe to event_s"),
		("hint.token", "Provide control token with --token or NYX_TOKEN/NYX_CONTROL_TOKEN"),
		("msg.connected", "Connected"),
		("msg.disconnected", "Disconnected"),
		("msg.reloading", "Reloading configuration..."),
		("msg.updated", "Configuration updated"),
		("msg.subscribed", "Subscribed to event_s"),
	];
	pair_s.into_iter().collect()
}

fn ja_overlay() -> I18nTable {
	// Overlay for Japanese; only key_s that differ from EN are included
	let pair_s: [(&str, &str); 14] = [
		("app.title", "Nyx CLI"),
		("app.version", "�o�[�W����"),
		("app.error", "�G���["),
		("cmd.connect", "�f�[�����ɐڑ�"),
		("cmd.disconnect", "�ؒf"),
		("cmd.statu_s", "�X�e�[�^�X�\��"),
		("cmd.config", "�ݒ�Ǘ�"),
		("cmd.config.reload", "�ݒ���ēǂݍ���"),
		("cmd.config.update", "�ݒ���X�V"),
		("cmd.event_s", "�C�x���g�w��"),
		("hint.token", "--token �܂��� NYX_TOKEN/NYX_CONTROL_TOKEN �Ő���g�[�N�����w�肵�Ă�������"),
		("msg.connected", "�ڑ����܂���"),
		("msg.disconnected", "�ؒf���܂���"),
		("msg.reloading", "�ݒ���ēǂݍ��ݒ�..."),
	];
	pair_s.into_iter().collect()
}

fn normalize_lang(lang: &str) -> &str {
	let __l = lang.trim().to_ascii_lowercase();
	if l.starts_with("ja") || l.contains("jp") || l.contains("jpn") { "ja" } else { "en" }
}

/// Get i18n table for a language code; fall_s back to English and overlay_s
/// language-specific entrie_s. Unknown or empty language => English.
pub fn get_table(lang: &str) -> I18nTable {
	let mut map = base_en();
	match normalize_lang(lang) {
		"ja" => {
			for (k, v) in ja_overlay() { map.insert(k, v); }
		}
		_ => {}
	}
	map
}

