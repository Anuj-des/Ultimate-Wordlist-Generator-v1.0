import tkinter as tk
from tkinter import ttk, messagebox, filedialog, scrolledtext
import itertools
import os
import re
import threading
import math
import json
import time
import hashlib
from datetime import datetime, timedelta
from collections import Counter, defaultdict
import pandas as pd
import numpy as np
from reportlab.lib.pagesizes import letter, A4
from reportlab.platypus import SimpleDocTemplate, Table, TableStyle, Paragraph, Spacer
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib import colors
from reportlab.lib.units import inch
import zipfile
import sqlite3
from pathlib import Path
import webbrowser
import random
import schedule
import time as time_module
from difflib import SequenceMatcher
import heapq
from concurrent.futures import ThreadPoolExecutor, as_completed

class UltimateWordlistGenerator:
    def __init__(self, root):
        self.root = root
        self.root.title("🔐 Ultimate Wordlist Generator v1.0")
        
        # Optimize window size
        screen_width = root.winfo_screenwidth()
        screen_height = root.winfo_screenheight()
        window_width = min(1200, screen_width - 100)
        window_height = min(900, screen_height - 100)
        
        x = (screen_width - window_width) // 2
        y = (screen_height - window_height) // 2
        
        self.root.geometry(f"{window_width}x{window_height}+{x}+{y}")
        self.root.minsize(1000, 700)
        
        # Initialize theme system
        self.current_theme = "professional_dark"
        self.setup_themes()
        
        # Initialize variables
        self.words = []
        self.repetitions = {}
        self.word_to_item = {}
        self.generation_thread = None
        self.stop_generation = False
        self.current_project = None
        self.templates = {}
        self.load_templates()
        
        # Wordlist Organizer variables
        self.current_wordlist = []
        self.organized_wordlists = {}
        self.organization_profiles = {}
        
        # Advanced character sets
        self.setup_character_sets()
        
        # Advanced patterns database
        self.setup_patterns_database()
        
        # Load organization profiles
        self.load_organization_profiles()
        
        self.setup_ui()
        self.apply_theme("professional_dark")
        
    def setup_character_sets(self):
        """Setup comprehensive character sets"""
        self.character_sets = {
            'lowercase': 'abcdefghijklmnopqrstuvwxyz',
            'uppercase': 'ABCDEFGHIJKLMNOPQRSTUVWXYZ',
            'numbers': '0123456789',
            'special_basic': '!@#$%^&*()_+-=',
            'special_extended': '[]{}|;:,.<>?/~`',
            'special_advanced': '"\'\\€£¥¢§©®™',
            'space': ' ',
            'unicode_basic': 'áéíóúñü¿¡'
        }
        
        # Leet speak levels
        self.leet_levels = {
            "basic": {
                'a': '@', 'e': '3', 'i': '1', 'o': '0', 's': '5', 't': '7',
                'b': '8', 'g': '9', 'l': '1'
            },
            "advanced": {
                'a': ['@', '4'], 'e': ['3', '€'], 'i': ['1', '!', '|'], 
                'o': ['0', '()'], 's': ['5', '$', 'z'], 't': ['7', '+'],
                'b': ['8', '|3'], 'g': ['9', '6'], 'h': ['#', '|-|'],
                'l': ['1', '|_'], 'z': ['2', '%']
            },
            "aggressive": {
                'a': ['@', '4', '^', '/\\', '∂'], 
                'e': ['3', '€', '&', '£', 'ë'],
                'i': ['1', '!', '|', '][', 'ï'], 
                'o': ['0', '()', '[]', '<>', 'ø'],
                's': ['5', '$', 'z', '§', '2'],
                't': ['7', '+', '†', '┴'],
                'b': ['8', '|3', '13', '!3', 'ß'],
                'g': ['9', '6', '&', 'ç'],
                'h': ['#', '|-|', '}{', ']-[', '♡'],
                'l': ['1', '|_', '£', '¬']
            }
        }
        
    def setup_patterns_database(self):
        """Setup comprehensive patterns database"""
        self.patterns_db = {
            # Keyboard walks
            "keyboard_walks": {
                "qwerty": "qwertyuiopasdfghjklzxcvbnm",
                "qwerty_shift": "QWERTYUIOPASDFGHJKLZXCVBNM",
                "qwerty_top_row": "qwertyuiop",
                "qwerty_mid_row": "asdfghjkl",
                "qwerty_bottom_row": "zxcvbnm",
                "keypad": "1234567890",
                "keypad_alt": "7894561230",
                "keypad_reverse": "0987654321"
            },
            
            # Common number sequences
            "number_sequences": [
                "123", "1234", "12345", "123456", "1234567", "12345678", "123456789", "1234567890",
                "111", "1111", "11111", "111111",
                "121", "1212", "121212",
                "112", "1122", "112233",
                "123123", "12341234",
                "999", "9999", "99999",
                "000", "0000", "00000",
                "101", "1010", "101010",
                "202", "2020", "202020",
                "010", "0101", "010101",
                "110", "1122", "1133",
                "111222", "111222333",
                "13579", "24680",
                "100", "1000", "10000",
                "200", "2000", "20000",
                "500", "5000", "50000"
            ],
            
            # Date formats
            "date_formats": [
                "0101", "01011970", "010170", "011970",
                "1010", "10101980", "101080", "101980",
                "2501", "25011990", "250190", "251990",
                "3112", "31121999", "311299", "3112999",
                "1970", "1971", "1972", "1973", "1974", "1975", 
                "1976", "1977", "1978", "1979", "1980", "1981",
                "1982", "1983", "1984", "1985", "1986", "1987",
                "1988", "1989", "1990", "1991", "1992", "1993",
                "1994", "1995", "1996", "1997", "1998", "1999",
                "2000", "2001", "2002", "2003", "2004", "2005",
                "2006", "2007", "2008", "2009", "2010", "2011",
                "2012", "2013", "2014", "2015", "2016", "2017",
                "2018", "2019", "2020", "2021", "2022", "2023", "2024"
            ],
            
            # Common password fragments
            "common_fragments": [
                "admin", "password", "pass", "pwd", "123", "!@#", "qwerty", 
                "abc", "xyz", "test", "demo", "temp", "backup", "secret", 
                "private", "secure", "system", "server", "client", "user", 
                "login", "auth", "access", "root", "guest", "default",
                "changeme", "letmein", "welcome", "master", "super", "admin123",
                "password123", "pass123", "pwd123", "qwerty123", "abc123",
                "test123", "demo123", "temp123", "secret123", "private123"
            ],
            
            # Social engineering patterns
            "social_patterns": {
                "family": ["son", "daughter", "wife", "husband", "mom", "dad", "father", "mother", 
                          "brother", "sister", "baby", "child", "kid", "family", "home"],
                "pets": ["dog", "cat", "bird", "fish", "pet", "puppy", "kitten", "rabbit", 
                        "hamster", "turtle", "parrot", "goldfish"],
                "sports": ["football", "soccer", "baseball", "basketball", "tennis", "golf", 
                          "cricket", "rugby", "hockey", "volleyball", "swimming", "running"],
                "hobbies": ["music", "movie", "game", "book", "car", "photo", "art", "draw", 
                           "paint", "read", "write", "code", "travel", "cook", "garden"],
                "seasons": ["spring", "summer", "autumn", "winter", "fall"],
                "months": ["january", "february", "march", "april", "may", "june", 
                          "july", "august", "september", "october", "november", "december"],
                "days": ["monday", "tuesday", "wednesday", "thursday", "friday", "saturday", "sunday"]
            },
            
            # Company patterns
            "company_patterns": {
                "departments": ["IT", "HR", "Finance", "Sales", "Marketing", "Admin", "Support", 
                               "Engineering", "Development", "Operations", "Security"],
                "titles": ["manager", "director", "assistant", "engineer", "analyst", "specialist",
                          "coordinator", "administrator", "supervisor", "officer", "executive"],
                "locations": ["ny", "la", "sf", "london", "tokyo", "berlin", "paris", "sydney",
                             "toronto", "mumbai", "singapore", "dublin", "amsterdam"],
                "products": ["v1", "v2", "pro", "lite", "enterprise", "cloud", "mobile", "web",
                            "desktop", "server", "network", "security", "backup"]
            }
        }
        
    def setup_themes(self):
        """Setup multiple professional color themes"""
        self.themes = {
            "professional_dark": {
                "name": "Professional Dark",
                "bg": "#1e1e1e",
                "fg": "#ffffff",
                "secondary_bg": "#2d2d30",
                "accent": "#007acc",
                "accent_light": "#3c3c3c",
                "text_bg": "#252526",
                "text_fg": "#cccccc",
                "button_bg": "#333333",
                "button_fg": "#ffffff",
                "success": "#4EC9B0",
                "warning": "#FFC608",
                "error": "#F44747",
                "tree_bg": "#252526",
                "tree_fg": "#cccccc"
            },
            "blue_dark": {
                "name": "Blue Dark",
                "bg": "#0a1929",
                "fg": "#e3f2fd",
                "secondary_bg": "#1e2a3a",
                "accent": "#2196f3",
                "accent_light": "#1976d2",
                "text_bg": "#152642",
                "text_fg": "#bbdefb",
                "button_bg": "#1565c0",
                "button_fg": "#e3f2fd",
                "success": "#4caf50",
                "warning": "#ff9800",
                "error": "#f44336",
                "tree_bg": "#152642",
                "tree_fg": "#bbdefb"
            },
            "green_dark": {
                "name": "Green Dark",
                "bg": "#1a1f1c",
                "fg": "#e8f5e8",
                "secondary_bg": "#2a332a",
                "accent": "#4caf50",
                "accent_light": "#388e3c",
                "text_bg": "#223322",
                "text_fg": "#c8e6c9",
                "button_bg": "#2e7d32",
                "button_fg": "#e8f5e8",
                "success": "#66bb6a",
                "warning": "#ffb74d",
                "error": "#ef5350",
                "tree_bg": "#223322",
                "tree_fg": "#c8e6c9"
            },
            "purple_dark": {
                "name": "Purple Dark",
                "bg": "#1a1b26",
                "fg": "#e1d5e7",
                "secondary_bg": "#2a2b3a",
                "accent": "#9c27b0",
                "accent_light": "#7b1fa2",
                "text_bg": "#222233",
                "text_fg": "#d1c4e9",
                "button_bg": "#6a1b9a",
                "button_fg": "#e1d5e7",
                "success": "#7e57c2",
                "warning": "#ffab40",
                "error": "#ec407a",
                "tree_bg": "#222233",
                "tree_fg": "#d1c4e9"
            },
            "professional_light": {
                "name": "Professional Light",
                "bg": "#f5f5f5",
                "fg": "#333333",
                "secondary_bg": "#ffffff",
                "accent": "#007acc",
                "accent_light": "#e1f5fe",
                "text_bg": "#ffffff",
                "text_fg": "#212121",
                "button_bg": "#e0e0e0",
                "button_fg": "#333333",
                "success": "#2e7d32",
                "warning": "#f57c00",
                "error": "#d32f2f",
                "tree_bg": "#ffffff",
                "tree_fg": "#212121"
            }
        }
        
    def setup_ui(self):
        # Create style
        self.style = ttk.Style()
        self.style.theme_use('clam')
        
        # Create main notebook
        self.notebook = ttk.Notebook(self.root)
        self.notebook.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Create all tabs
        self.basic_tab = ttk.Frame(self.notebook)
        self.advanced_tab = ttk.Frame(self.notebook)
        self.character_tab = ttk.Frame(self.notebook)
        self.batch_tab = ttk.Frame(self.notebook)
        self.analytics_tab = ttk.Frame(self.notebook)
        self.settings_tab = ttk.Frame(self.notebook)
        self.manual_tab = ttk.Frame(self.notebook)
        self.organizer_tab = ttk.Frame(self.notebook)  # New Wordlist Organizer tab
        
        self.notebook.add(self.basic_tab, text="🎯 Basic Generator")
        self.notebook.add(self.advanced_tab, text="⚡ Advanced Rules")
        self.notebook.add(self.character_tab, text="🔤 Character Options")
        self.notebook.add(self.batch_tab, text="📊 Batch Processing")
        self.notebook.add(self.analytics_tab, text="📈 Analytics")
        self.notebook.add(self.settings_tab, text="⚙️ Settings")
        self.notebook.add(self.manual_tab, text="📖 User Manual")
        self.notebook.add(self.organizer_tab, text="🗂️ Wordlist Organizer")  # New tab
        
        self.setup_basic_tab()
        self.setup_advanced_tab()
        self.setup_character_tab()
        self.setup_batch_tab()
        self.setup_analytics_tab()
        self.setup_settings_tab()
        self.setup_manual_tab()
        self.setup_organizer_tab()  # Setup the new organizer tab
        
        # Status bar
        self.status_frame = tk.Frame(self.root)
        self.status_frame.pack(fill=tk.X, side=tk.BOTTOM)
        
        self.status_label = tk.Label(self.status_frame, text="Ready - Ultimate Wordlist Generator v4.0", anchor=tk.W)
        self.status_label.pack(side=tk.LEFT, padx=10, pady=2)
        
        self.progress = ttk.Progressbar(self.status_frame, mode='determinate')
        self.progress.pack(side=tk.RIGHT, padx=10, pady=2, fill=tk.X, expand=True)
        
    def setup_basic_tab(self):
        # Main frame
        main_frame = ttk.Frame(self.basic_tab)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Left frame - Input
        left_frame = ttk.Frame(main_frame)
        left_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 5))
        
        # Right frame - Preview
        right_frame = ttk.Frame(main_frame)
        right_frame.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, padx=(5, 0))
        
        # Input section
        input_frame = ttk.LabelFrame(left_frame, text="📥 Input Sources", padding=10)
        input_frame.pack(fill=tk.X, pady=5)
        
        # Manual input
        manual_frame = ttk.Frame(input_frame)
        manual_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(manual_frame, text="Add Word:").pack(side=tk.LEFT)
        self.word_entry = ttk.Entry(manual_frame, width=20)
        self.word_entry.pack(side=tk.LEFT, padx=5)
        self.word_entry.bind('<Return>', lambda e: self.add_word())
        
        ttk.Label(manual_frame, text="Max Rep:").pack(side=tk.LEFT, padx=(10,0))
        self.rep_entry = ttk.Entry(manual_frame, width=5)
        self.rep_entry.pack(side=tk.LEFT, padx=5)
        self.rep_entry.insert(0, "2")
        
        ttk.Button(manual_frame, text="Add", command=self.add_word).pack(side=tk.LEFT, padx=5)
        
        # File import buttons
        file_frame = ttk.Frame(input_frame)
        file_frame.pack(fill=tk.X, pady=5)
        
        ttk.Button(file_frame, text="Import Text", 
                  command=self.import_from_text).pack(side=tk.LEFT, padx=2)
        ttk.Button(file_frame, text="Import CSV", 
                  command=self.import_from_csv).pack(side=tk.LEFT, padx=2)
        ttk.Button(file_frame, text="Paste Clipboard", 
                  command=self.paste_from_clipboard).pack(side=tk.LEFT, padx=2)
        
        # Words list
        list_frame = ttk.LabelFrame(left_frame, text="📋 Word List", padding=10)
        list_frame.pack(fill=tk.BOTH, expand=True, pady=5)
        
        # Treeview for words
        columns = ('Word', 'Max Repetitions')
        self.tree = ttk.Treeview(list_frame, columns=columns, show='headings')
        
        self.tree.heading('Word', text='Word')
        self.tree.heading('Max Repetitions', text='Max Rep')
        
        self.tree.column('Word', width=250, minwidth=150)
        self.tree.column('Max Repetitions', width=80, minwidth=60)
        
        scrollbar = ttk.Scrollbar(list_frame, orient=tk.VERTICAL, command=self.tree.yview)
        self.tree.configure(yscrollcommand=scrollbar.set)
        
        self.tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        # Control buttons
        control_frame = ttk.Frame(left_frame)
        control_frame.pack(fill=tk.X, pady=5)
        
        ttk.Button(control_frame, text="Remove Selected", 
                  command=self.remove_word).pack(side=tk.LEFT, padx=2)
        ttk.Button(control_frame, text="Clear All", 
                  command=self.clear_all).pack(side=tk.LEFT, padx=2)
        ttk.Button(control_frame, text="Edit Selected", 
                  command=self.edit_word).pack(side=tk.LEFT, padx=2)
        
        # Generation options
        gen_frame = ttk.LabelFrame(left_frame, text="⚙️ Generation Options", padding=10)
        gen_frame.pack(fill=tk.X, pady=5)
        
        self.permutations_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(gen_frame, text="All Permutations", 
                       variable=self.permutations_var).pack(anchor=tk.W)
        
        self.case_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(gen_frame, text="Case Variations", 
                       variable=self.case_var).pack(anchor=tk.W)
        
        self.leet_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(gen_frame, text="Leet Speak", 
                       variable=self.leet_var).pack(anchor=tk.W)
        
        # Right frame - Preview and output
        preview_frame = ttk.LabelFrame(right_frame, text="👁️ Preview", padding=10)
        preview_frame.pack(fill=tk.BOTH, expand=True, pady=5)
        
        self.preview_text = scrolledtext.ScrolledText(preview_frame, height=12, width=40)
        self.preview_text.pack(fill=tk.BOTH, expand=True)
        
        # Output options
        output_frame = ttk.LabelFrame(right_frame, text="📤 Output Options", padding=10)
        output_frame.pack(fill=tk.X, pady=5)
        
        # Format selection
        format_frame = ttk.Frame(output_frame)
        format_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(format_frame, text="Format:").pack(side=tk.LEFT)
        self.format_var = tk.StringVar(value="txt")
        formats = [("Text", "txt"), ("PDF", "pdf"), ("Excel", "xlsx"), 
                  ("JSON", "json"), ("SQLite", "db"), ("ZIP", "zip")]
        
        format_subframe = ttk.Frame(format_frame)
        format_subframe.pack(side=tk.LEFT, fill=tk.X, expand=True)
        
        for i, (text, value) in enumerate(formats):
            ttk.Radiobutton(format_subframe, text=text, variable=self.format_var, 
                           value=value).pack(side=tk.LEFT, padx=5)
            if i == 2:  # Break after 3 options
                format_subframe = ttk.Frame(format_frame)
                format_subframe.pack(side=tk.LEFT, fill=tk.X, expand=True)
        
        # Advanced options
        adv_frame = ttk.Frame(output_frame)
        adv_frame.pack(fill=tk.X, pady=5)
        
        self.deduplicate_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(adv_frame, text="Remove Duplicates", 
                       variable=self.deduplicate_var).pack(side=tk.LEFT, padx=5)
        
        self.sort_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(adv_frame, text="Sort Output", 
                       variable=self.sort_var).pack(side=tk.LEFT, padx=5)
        
        # Generate button
        generate_btn = ttk.Button(right_frame, text="🚀 Generate Wordlist", 
                                 command=self.generate_wordlist)
        generate_btn.pack(pady=10, fill=tk.X)
        
        # Statistics
        stats_frame = ttk.LabelFrame(right_frame, text="📊 Statistics", padding=10)
        stats_frame.pack(fill=tk.X, pady=5)
        
        self.stats_label = ttk.Label(stats_frame, text="Words: 0 | Total Positions: 0 | Estimated: 0")
        self.stats_label.pack(anchor=tk.W)
        
    def setup_advanced_tab(self):
        # Main frame with proper expansion
        main_frame = ttk.Frame(self.advanced_tab)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Create a paned window for better layout control
        paned_window = ttk.PanedWindow(main_frame, orient=tk.VERTICAL)
        paned_window.pack(fill=tk.BOTH, expand=True)
        
        # Top section - Enhanced Rule-Based Generation
        top_frame = ttk.Frame(paned_window)
        paned_window.add(top_frame, weight=1)
        
        # Enhanced Rule-Based Generation
        rule_frame = ttk.LabelFrame(top_frame, text="🎯 Enhanced Rule-Based Generation", padding=15)
        rule_frame.pack(fill=tk.BOTH, expand=True, pady=5)
        
        # Create a notebook-like structure with frames
        rules_notebook = ttk.Frame(rule_frame)
        rules_notebook.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Rule options in three columns with proper distribution
        rules_container = ttk.Frame(rules_notebook)
        rules_container.pack(fill=tk.BOTH, expand=True)
        
        # Configure grid for equal distribution
        rules_container.columnconfigure(0, weight=1)
        rules_container.columnconfigure(1, weight=1)
        rules_container.columnconfigure(2, weight=1)
        
        # Initialize rule variables
        self.rule_vars = {}
        
        # Column 1 - Basic Rules
        rules_col1 = ttk.LabelFrame(rules_container, text="Basic Rules", padding=10)
        rules_col1.grid(row=0, column=0, sticky="nsew", padx=5, pady=5)
        
        basic_rules = [
            ("Add common suffixes (123, !, @)", "suffixes"),
            ("Add common prefixes", "prefixes"),
            ("Capitalize variations", "capitalize"),
            ("Reverse words", "reverse"),
            ("Duplicate words", "duplicate"),
        ]
        
        for text, key in basic_rules:
            self.rule_vars[key] = tk.BooleanVar()
            chk = ttk.Checkbutton(rules_col1, text=text, variable=self.rule_vars[key])
            chk.pack(anchor=tk.W, pady=3, fill=tk.X)
        
        # Column 2 - Advanced Rules
        rules_col2 = ttk.LabelFrame(rules_container, text="Advanced Rules", padding=10)
        rules_col2.grid(row=0, column=1, sticky="nsew", padx=5, pady=5)
        
        advanced_rules = [
            ("Toggle case randomly", "toggle_case"),
            ("Add birth years (1950-2024)", "years"),
            ("Add common substitutions", "substitutions"),
            ("Keyboard walk patterns", "keyboard_walk"),
            ("Number sequences", "number_sequences"),
        ]
        
        for text, key in advanced_rules:
            self.rule_vars[key] = tk.BooleanVar()
            chk = ttk.Checkbutton(rules_col2, text=text, variable=self.rule_vars[key])
            chk.pack(anchor=tk.W, pady=3, fill=tk.X)
        
        # Column 3 - Expert Rules
        rules_col3 = ttk.LabelFrame(rules_container, text="Expert Rules", padding=10)
        rules_col3.grid(row=0, column=2, sticky="nsew", padx=5, pady=5)
        
        expert_rules = [
            ("Date patterns", "date_patterns"),
            ("Common fragments", "common_fragments"),
            ("Social engineering", "social_patterns"),
            ("Company patterns", "company_patterns"),
            ("Seasonal patterns", "seasonal_patterns"),
        ]
        
        for text, key in expert_rules:
            self.rule_vars[key] = tk.BooleanVar()
            chk = ttk.Checkbutton(rules_col3, text=text, variable=self.rule_vars[key])
            chk.pack(anchor=tk.W, pady=3, fill=tk.X)
        
        # Bottom section - Other controls
        bottom_frame = ttk.Frame(paned_window)
        paned_window.add(bottom_frame, weight=1)
        
        # Create notebook for bottom section
        bottom_notebook = ttk.Notebook(bottom_frame)
        bottom_notebook.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Tab 1: Pattern Generation
        pattern_tab = ttk.Frame(bottom_notebook)
        bottom_notebook.add(pattern_tab, text="Pattern Generation")
        
        # Pattern-based generation
        pattern_frame = ttk.LabelFrame(pattern_tab, text="🔤 Custom Patterns", padding=10)
        pattern_frame.pack(fill=tk.BOTH, expand=True, pady=5)
        
        ttk.Label(pattern_frame, text="Custom Patterns (one per line):", font=('Arial', 10, 'bold')).pack(anchor=tk.W, pady=(0, 5))
        
        self.pattern_text = scrolledtext.ScrolledText(pattern_frame, height=8, wrap=tk.WORD)
        self.pattern_text.pack(fill=tk.BOTH, expand=True, pady=5)
        
        # Load common patterns
        common_patterns = "\n".join(self.patterns_db["number_sequences"][:20])
        self.pattern_text.insert("1.0", common_patterns)
        
        # Tab 2: Markov Generation
        markov_tab = ttk.Frame(bottom_notebook)
        bottom_notebook.add(markov_tab, text="Markov Chains")
        
        # Markov generation
        markov_frame = ttk.LabelFrame(markov_tab, text="🎲 Markov Chain Generation", padding=10)
        markov_frame.pack(fill=tk.BOTH, expand=True, pady=5)
        
        markov_controls = ttk.Frame(markov_frame)
        markov_controls.pack(fill=tk.X, pady=10, padx=10)
        
        # Markov controls in a grid
        ttk.Label(markov_controls, text="Markov Order:").grid(row=0, column=0, sticky=tk.W, padx=(0, 10))
        self.markov_order = ttk.Spinbox(markov_controls, from_=2, to=5, width=8)
        self.markov_order.set(3)
        self.markov_order.grid(row=0, column=1, sticky=tk.W, padx=(0, 20))
        
        ttk.Label(markov_controls, text="Generate:").grid(row=0, column=2, sticky=tk.W, padx=(0, 10))
        self.markov_count = ttk.Spinbox(markov_controls, from_=100, to=10000, width=10)
        self.markov_count.set(1000)
        self.markov_count.grid(row=0, column=3, sticky=tk.W)
        
        # Generate button
        ttk.Button(markov_controls, text="Generate Markov Passwords", 
                  command=self.generate_markov).grid(row=1, column=0, columnspan=4, pady=10)
        
        # Tab 3: Password Strength
        strength_tab = ttk.Frame(bottom_notebook)
        bottom_notebook.add(strength_tab, text="Password Strength")
        
        # Password strength settings
        strength_frame = ttk.LabelFrame(strength_tab, text="🛡️ Password Strength Settings", padding=10)
        strength_frame.pack(fill=tk.BOTH, expand=True, pady=5)
        
        strength_grid = ttk.Frame(strength_frame)
        strength_grid.pack(fill=tk.X, pady=10, padx=10)
        
        # Length settings row
        length_frame = ttk.Frame(strength_grid)
        length_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(length_frame, text="Min Length:").pack(side=tk.LEFT)
        self.min_length_var = tk.StringVar(value="1")
        ttk.Entry(length_frame, textvariable=self.min_length_var, width=5).pack(side=tk.LEFT, padx=5)
        
        ttk.Label(length_frame, text="Max Length:").pack(side=tk.LEFT, padx=(20, 0))
        self.max_length_var = tk.StringVar(value="100")
        ttk.Entry(length_frame, textvariable=self.max_length_var, width=5).pack(side=tk.LEFT, padx=5)
        
        # Character requirements in a grid
        req_frame = ttk.Frame(strength_grid)
        req_frame.pack(fill=tk.X, pady=10)
        
        self.require_upper_var = tk.BooleanVar()
        ttk.Checkbutton(req_frame, text="Require Uppercase", 
                       variable=self.require_upper_var).grid(row=0, column=0, sticky=tk.W, padx=(0, 20))
        
        self.require_lower_var = tk.BooleanVar()
        ttk.Checkbutton(req_frame, text="Require Lowercase", 
                       variable=self.require_lower_var).grid(row=0, column=1, sticky=tk.W, padx=(0, 20))
        
        self.require_digit_var = tk.BooleanVar()
        ttk.Checkbutton(req_frame, text="Require Digit", 
                       variable=self.require_digit_var).grid(row=1, column=0, sticky=tk.W, padx=(0, 20))
        
        self.require_special_var = tk.BooleanVar()
        ttk.Checkbutton(req_frame, text="Require Special", 
                       variable=self.require_special_var).grid(row=1, column=1, sticky=tk.W)
        
        # Configure grid weights for proper expansion
        req_frame.columnconfigure(0, weight=1)
        req_frame.columnconfigure(1, weight=1)
        
    def setup_character_tab(self):
        """New tab for character set options with FIXED LAYOUT"""
        # Main frame with proper expansion
        main_frame = ttk.Frame(self.character_tab)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Create a paned window for better layout control
        paned_window = ttk.PanedWindow(main_frame, orient=tk.VERTICAL)
        paned_window.pack(fill=tk.BOTH, expand=True)
        
        # Top section - Character Sets
        top_frame = ttk.Frame(paned_window)
        paned_window.add(top_frame, weight=1)
        
        # Character Set Selection
        charset_frame = ttk.LabelFrame(top_frame, text="🔤 Character Set Selection", padding=15)
        charset_frame.pack(fill=tk.BOTH, expand=True, pady=5)
        
        # Character set options in a proper grid
        self.charset_vars = {}
        charset_options = [
            ("Lowercase (a-z)", "lowercase", True),
            ("Uppercase (A-Z)", "uppercase", True),
            ("Numbers (0-9)", "numbers", True),
            ("Basic Special (!@#$%^&*()_+-=)", "special_basic", True),
            ("Extended Special ([]{}|;:,.<>?/~`)", "special_extended", False),
            ("Advanced Special (\"'\\€£¥¢§©®™)", "special_advanced", False),
            ("Space ( )", "space", False),
            ("Unicode Basic (áéíóúñü¿¡)", "unicode_basic", False)
        ]
        
        # Create a grid with 2 columns
        charset_grid = ttk.Frame(charset_frame)
        charset_grid.pack(fill=tk.BOTH, expand=True, pady=10)
        
        # Configure grid columns for equal spacing
        charset_grid.columnconfigure(0, weight=1)
        charset_grid.columnconfigure(1, weight=1)
        
        for i, (text, key, default) in enumerate(charset_options):
            self.charset_vars[key] = tk.BooleanVar(value=default)
            row = i // 2
            col = i % 2
            
            # Create frame for each checkbox to ensure proper alignment
            chk_frame = ttk.Frame(charset_grid)
            chk_frame.grid(row=row, column=col, sticky=tk.W, padx=15, pady=8)
            
            ttk.Checkbutton(chk_frame, text=text, variable=self.charset_vars[key]).pack(anchor=tk.W)
        
        # Bottom section - Other character options
        bottom_frame = ttk.Frame(paned_window)
        paned_window.add(bottom_frame, weight=1)
        
        # Create notebook for bottom section
        bottom_notebook = ttk.Notebook(bottom_frame)
        bottom_notebook.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Tab 1: Leet Speak
        leet_tab = ttk.Frame(bottom_notebook)
        bottom_notebook.add(leet_tab, text="Leet Speak")
        
        # Leet Speak Levels
        leet_frame = ttk.LabelFrame(leet_tab, text="💀 Leet Speak Levels", padding=15)
        leet_frame.pack(fill=tk.BOTH, expand=True, pady=5)
        
        self.leet_level_var = tk.StringVar(value="basic")
        leet_levels = [
            ("Basic Leet (a=@, e=3, i=1)", "basic"),
            ("Advanced Leet (multiple substitutions)", "advanced"),
            ("Aggressive Leet (maximum substitutions)", "aggressive")
        ]
        
        for text, value in leet_levels:
            ttk.Radiobutton(leet_frame, text=text, variable=self.leet_level_var, 
                           value=value).pack(anchor=tk.W, pady=8)
        
        # Tab 2: Custom Characters
        custom_tab = ttk.Frame(bottom_notebook)
        bottom_notebook.add(custom_tab, text="Custom Characters")
        
        # Custom Character Sets
        custom_frame = ttk.LabelFrame(custom_tab, text="🎨 Custom Character Sets", padding=15)
        custom_frame.pack(fill=tk.BOTH, expand=True, pady=5)
        
        # Custom characters
        custom_chars_frame = ttk.Frame(custom_frame)
        custom_chars_frame.pack(fill=tk.X, pady=10, padx=10)
        
        ttk.Label(custom_chars_frame, text="Custom Characters:").pack(anchor=tk.W)
        self.custom_chars_var = tk.StringVar()
        custom_entry = ttk.Entry(custom_chars_frame, textvariable=self.custom_chars_var, width=50)
        custom_entry.pack(fill=tk.X, pady=5)
        custom_entry.insert(0, "!@#$%")
        
        # Exclude characters
        exclude_frame = ttk.Frame(custom_frame)
        exclude_frame.pack(fill=tk.X, pady=10, padx=10)
        
        ttk.Label(exclude_frame, text="Exclude Characters:").pack(anchor=tk.W)
        self.exclude_chars_var = tk.StringVar()
        exclude_entry = ttk.Entry(exclude_frame, textvariable=self.exclude_chars_var, width=50)
        exclude_entry.pack(fill=tk.X, pady=5)
        exclude_entry.insert(0, "oO0l1i")
        
        # Tab 3: Character Preview
        preview_tab = ttk.Frame(bottom_notebook)
        bottom_notebook.add(preview_tab, text="Character Preview")
        
        # Character Set Preview
        preview_frame = ttk.LabelFrame(preview_tab, text="👁️ Character Set Preview", padding=15)
        preview_frame.pack(fill=tk.BOTH, expand=True, pady=5)
        
        self.charset_preview_text = scrolledtext.ScrolledText(preview_frame, height=6, wrap=tk.WORD)
        self.charset_preview_text.pack(fill=tk.BOTH, expand=True, pady=10, padx=10)
        
        # Preview button
        preview_btn_frame = ttk.Frame(preview_frame)
        preview_btn_frame.pack(fill=tk.X, pady=5, padx=10)
        
        ttk.Button(preview_btn_frame, text="Update Preview", 
                  command=self.update_charset_preview).pack()
        
        # Initial preview update
        self.update_charset_preview()
        
    def setup_batch_tab(self):
        main_frame = ttk.Frame(self.batch_tab)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Template management
        template_frame = ttk.LabelFrame(main_frame, text="📁 Template Management", padding=10)
        template_frame.pack(fill=tk.X, pady=5)
        
        ttk.Button(template_frame, text="Save Current as Template", 
                  command=self.save_template).pack(side=tk.LEFT, padx=5)
        ttk.Button(template_frame, text="Load Template", 
                  command=self.load_template).pack(side=tk.LEFT, padx=5)
        ttk.Button(template_frame, text="Manage Templates", 
                  command=self.manage_templates).pack(side=tk.LEFT, padx=5)
        
        # Batch processing
        batch_frame = ttk.LabelFrame(main_frame, text="🔄 Batch Processing", padding=10)
        batch_frame.pack(fill=tk.X, pady=5)
        
        ttk.Button(batch_frame, text="Process Multiple Files", 
                  command=self.batch_process).pack(side=tk.LEFT, padx=5)
        ttk.Button(batch_frame, text="Schedule Generation", 
                  command=self.schedule_generation).pack(side=tk.LEFT, padx=5)
        
        # Project management
        project_frame = ttk.LabelFrame(main_frame, text="💼 Project Management", padding=10)
        project_frame.pack(fill=tk.X, pady=5)
        
        ttk.Button(project_frame, text="New Project", 
                  command=self.new_project).pack(side=tk.LEFT, padx=5)
        ttk.Button(project_frame, text="Save Project", 
                  command=self.save_project).pack(side=tk.LEFT, padx=5)
        ttk.Button(project_frame, text="Load Project", 
                  command=self.load_project).pack(side=tk.LEFT, padx=5)
        
    def setup_analytics_tab(self):
        main_frame = ttk.Frame(self.analytics_tab)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Password strength analysis
        strength_frame = ttk.LabelFrame(main_frame, text="🛡️ Password Strength Analysis", padding=10)
        strength_frame.pack(fill=tk.X, pady=5)
        
        ttk.Button(strength_frame, text="Analyze Generated Wordlist", 
                  command=self.analyze_strength).pack(side=tk.LEFT, padx=5)
        ttk.Button(strength_frame, text="Compare Wordlists", 
                  command=self.compare_wordlists).pack(side=tk.LEFT, padx=5)
        
        # Statistics display
        stats_frame = ttk.LabelFrame(main_frame, text="📈 Statistics", padding=10)
        stats_frame.pack(fill=tk.BOTH, expand=True, pady=5)
        
        self.stats_text = scrolledtext.ScrolledText(stats_frame, height=15)
        self.stats_text.pack(fill=tk.BOTH, expand=True)
        
    def setup_settings_tab(self):
        main_frame = ttk.Frame(self.settings_tab)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Performance settings
        perf_frame = ttk.LabelFrame(main_frame, text="⚡ Performance Settings", padding=10)
        perf_frame.pack(fill=tk.X, pady=5)
        
        perf_subframe = ttk.Frame(perf_frame)
        perf_subframe.pack(fill=tk.X)
        
        ttk.Label(perf_subframe, text="Max Threads:").pack(side=tk.LEFT)
        self.thread_count = ttk.Spinbox(perf_subframe, from_=1, to=16, width=5)
        self.thread_count.set(4)
        self.thread_count.pack(side=tk.LEFT, padx=5)
        
        ttk.Label(perf_subframe, text="Chunk Size:").pack(side=tk.LEFT, padx=(20,0))
        self.chunk_size = ttk.Spinbox(perf_subframe, from_=1000, to=100000, width=8)
        self.chunk_size.set(10000)
        self.chunk_size.pack(side=tk.LEFT, padx=5)
        
        # Security settings
        security_frame = ttk.LabelFrame(main_frame, text="🔒 Security Settings", padding=10)
        security_frame.pack(fill=tk.X, pady=5)
        
        self.auto_clear_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(security_frame, text="Auto-clear sensitive data", 
                       variable=self.auto_clear_var).pack(anchor=tk.W)
        
        self.encrypt_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(security_frame, text="Encrypt project files", 
                       variable=self.encrypt_var).pack(anchor=tk.W)
        
        # UI Settings
        ui_frame = ttk.LabelFrame(main_frame, text="🎨 UI Theme Settings", padding=10)
        ui_frame.pack(fill=tk.X, pady=5)
        
        self.theme_var = tk.StringVar(value="professional_dark")
        theme_frame = ttk.Frame(ui_frame)
        theme_frame.pack(fill=tk.X, pady=5)
        
        themes = [
            ("Professional Dark", "professional_dark"),
            ("Blue Dark", "blue_dark"),
            ("Green Dark", "green_dark"),
            ("Purple Dark", "purple_dark"),
            ("Professional Light", "professional_light")
        ]
        
        for i, (text, value) in enumerate(themes):
            ttk.Radiobutton(theme_frame, text=text, variable=self.theme_var, 
                           value=value).pack(side=tk.LEFT, padx=10)
        
        ttk.Button(theme_frame, text="Apply Theme", 
                  command=self.apply_theme_from_settings).pack(side=tk.LEFT, padx=20)
        
    def setup_manual_tab(self):
        """User Manual Tab with comprehensive documentation"""
        main_frame = ttk.Frame(self.manual_tab)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Create notebook for manual sections
        manual_notebook = ttk.Notebook(main_frame)
        manual_notebook.pack(fill=tk.BOTH, expand=True)
        
        # Quick Start Guide
        quickstart_frame = ttk.Frame(manual_notebook)
        manual_notebook.add(quickstart_frame, text="🚀 Quick Start")
        
        quickstart_text = scrolledtext.ScrolledText(quickstart_frame, wrap=tk.WORD)
        quickstart_text.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        quickstart_content = """
ULTIMATE WORDLIST GENERATOR v4.0 - QUICK START GUIDE

🎯 BASIC USAGE:
1. Add words in the Basic Generator tab
2. Configure generation options
3. Generate and save your wordlist

📥 ADDING WORDS:
• Manual Entry: Type words and click Add
• File Import: Import from text/CSV files  
• Clipboard: Paste from clipboard
• Set Max Repetitions for each word

⚡ GENERATION OPTIONS:
• All Permutations: All possible arrangements
• Case Variations: UPPER/lower/Title case
• Leet Speak: Character substitutions
• Advanced Rules: Comprehensive pattern generation

🔤 CHARACTER OPTIONS:
• Select character sets to include
• Choose leet speak levels
• Define custom character sets
• Exclude specific characters

📊 OUTPUT FORMATS:
• TXT: Simple text file
• PDF: Formatted report
• Excel: Spreadsheet format
• JSON: Structured data
• SQLite: Database format
• ZIP: Compressed archive

💡 PRO TIPS:
• Start with 3-5 words for testing
• Use Max Repetitions 2-3 initially
• Enable rules gradually
• Preview before generating large lists

⚠️ SECURITY NOTE:
Only use for authorized security testing and educational purposes.
"""
        quickstart_text.insert('1.0', quickstart_content)
        quickstart_text.config(state=tk.DISABLED)
        
        # Advanced Features Guide
        advanced_frame = ttk.Frame(manual_notebook)
        manual_notebook.add(advanced_frame, text="⚡ Advanced Features")
        
        advanced_text = scrolledtext.ScrolledText(advanced_frame, wrap=tk.WORD)
        advanced_text.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        advanced_content = """
ADVANCED FEATURES GUIDE

🎯 RULE-BASED GENERATION:
• Common Suffixes: Add 123, !, @ to words
• Common Prefixes: Add patterns before words
• Capitalization: Multiple case variations
• Reverse: Create reversed versions
• Duplicate: Repeat words 2-3 times
• Keyboard Walks: Common keyboard patterns
• Number Sequences: Popular number patterns
• Date Patterns: Various date formats
• Social Engineering: Family, pets, hobbies
• Company Patterns: Departments, titles, products

🔤 CHARACTER SET OPTIONS:
Basic Sets:
• Lowercase (a-z)
• Uppercase (A-Z) 
• Numbers (0-9)
• Basic Special (!@#$%^&*()_+-=)

Advanced Sets:
• Extended Special ([]{}|;:,.<>?/~`)
• Advanced Special (\"'\\€£¥¢§©®™)
• Space character
• Unicode characters

💀 LEET SPEAK LEVELS:
Basic: a=@, e=3, i=1, o=0, s=5
Advanced: Multiple substitutions per character
Aggressive: Maximum substitutions including unicode

🎲 MARKOV CHAIN GENERATION:
• Generates intelligent password patterns
• Based on input word statistics
• Order: Context length (2-5)
• Count: Passwords to generate (100-10,000)

🛡️ PASSWORD STRENGTH SETTINGS:
• Minimum/Maximum length requirements
• Character type requirements
• Strength-based filtering
"""
        advanced_text.insert('1.0', advanced_content)
        advanced_text.config(state=tk.DISABLED)
        
        # Troubleshooting Guide
        trouble_frame = ttk.Frame(manual_notebook)
        manual_notebook.add(trouble_frame, text="🔧 Troubleshooting")
        
        trouble_text = scrolledtext.ScrolledText(trouble_frame, wrap=tk.WORD)
        trouble_text.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        trouble_content = """
TROUBLESHOOTING GUIDE

🚨 COMMON ISSUES:

1. MEMORY ERRORS:
• Reduce number of input words
• Lower Max Repetitions (2-3)
• Use Sequential Combinations
• Increase chunk size in settings

2. SLOW PERFORMANCE:
• Use fewer simultaneous rules
• Generate in smaller batches
• Increase thread count
• Close other applications

3. LARGE WORDLISTS:
• Start with 3-5 words for testing
• Enable rules gradually
• Use preview feature
• Set reasonable length limits

4. THEME ISSUES:
• Restart application
• Switch between themes
• Check system compatibility

5. FILE IMPORT PROBLEMS:
• Use UTF-8 encoding for text files
• Ensure CSV has words in first column
• Check file permissions

💡 PERFORMANCE TIPS:

For Quick Testing:
• 3-5 words, Max Rep 2, Basic rules

For Standard Use:
• 5-10 words, Max Rep 3, Moderate rules

For Comprehensive:
• 10-15 words, Max Rep 2, Multiple rules

For Large Scale:
• Batch processing, Multiple files

🔧 TECHNICAL SUPPORT:

System Requirements:
• Python 3.7+
• 4GB RAM (8GB recommended)
• 100MB free space

Dependencies:
• pandas, reportlab, openpyxl, numpy

Installation:
pip install pandas reportlab openpyxl numpy
"""
        trouble_text.insert('1.0', trouble_content)
        trouble_text.config(state=tk.DISABLED)

    def setup_organizer_tab(self):
        """Wordlist Organizer Tab with comprehensive organization features"""
        main_frame = ttk.Frame(self.organizer_tab)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Create notebook for organizer sections
        organizer_notebook = ttk.Notebook(main_frame)
        organizer_notebook.pack(fill=tk.BOTH, expand=True)
        
        # Tab 1: Basic Organization
        basic_org_frame = ttk.Frame(organizer_notebook)
        organizer_notebook.add(basic_org_frame, text="📊 Basic Organization")
        
        self.setup_basic_organization(basic_org_frame)
        
        # Tab 2: Advanced Filtering
        advanced_filter_frame = ttk.Frame(organizer_notebook)
        organizer_notebook.add(advanced_filter_frame, text="🔍 Advanced Filtering")
        
        self.setup_advanced_filtering(advanced_filter_frame)
        
        # Tab 3: Smart Segmentation
        segmentation_frame = ttk.Frame(organizer_notebook)
        organizer_notebook.add(segmentation_frame, text="📁 Smart Segmentation")
        
        self.setup_smart_segmentation(segmentation_frame)
        
        # Tab 4: Pattern Analysis
        pattern_frame = ttk.Frame(organizer_notebook)
        organizer_notebook.add(pattern_frame, text="🎯 Pattern Analysis")
        
        self.setup_pattern_analysis(pattern_frame)
        
        # Tab 5: Optimization
        optimization_frame = ttk.Frame(organizer_notebook)
        organizer_notebook.add(optimization_frame, text="⚡ Optimization")
        
        self.setup_optimization(optimization_frame)
        
        # Tab 6: Statistics & Analytics
        stats_frame = ttk.Frame(organizer_notebook)
        organizer_notebook.add(stats_frame, text="📈 Statistics")
        
        self.setup_organizer_statistics(stats_frame)
        
    def setup_basic_organization(self, parent):
        """Basic Organization Section"""
        # Main container with scrollbar
        container = ttk.Frame(parent)
        container.pack(fill=tk.BOTH, expand=True)
        
        # Create scrollable frame
        canvas = tk.Canvas(container)
        scrollbar = ttk.Scrollbar(container, orient="vertical", command=canvas.yview)
        scrollable_frame = ttk.Frame(canvas)
        
        scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        
        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        
        # Quick Stats Panel
        stats_frame = ttk.LabelFrame(scrollable_frame, text="📊 Quick Stats", padding=10)
        stats_frame.pack(fill=tk.X, pady=5, padx=5)
        
        self.org_stats_label = ttk.Label(stats_frame, text="No wordlist loaded")
        self.org_stats_label.pack(anchor=tk.W)
        
        # Load Wordlist Section
        load_frame = ttk.LabelFrame(scrollable_frame, text="📥 Load Wordlist", padding=10)
        load_frame.pack(fill=tk.X, pady=5, padx=5)
        
        ttk.Button(load_frame, text="Load Wordlist File", 
                  command=self.load_wordlist_for_org).pack(side=tk.LEFT, padx=5)
        ttk.Button(load_frame, text="Use Generated Wordlist", 
                  command=self.use_generated_wordlist).pack(side=tk.LEFT, padx=5)
        ttk.Button(load_frame, text="Clear Current", 
                  command=self.clear_current_wordlist).pack(side=tk.LEFT, padx=5)
        
        # Basic Sorting Section
        sort_frame = ttk.LabelFrame(scrollable_frame, text="🔄 Basic Sorting", padding=10)
        sort_frame.pack(fill=tk.X, pady=5, padx=5)
        
        # Length-based sorting
        length_sort_frame = ttk.Frame(sort_frame)
        length_sort_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(length_sort_frame, text="Length Sorting:").pack(side=tk.LEFT)
        ttk.Button(length_sort_frame, text="Shortest First", 
                  command=lambda: self.sort_wordlist('length_asc')).pack(side=tk.LEFT, padx=5)
        ttk.Button(length_sort_frame, text="Longest First", 
                  command=lambda: self.sort_wordlist('length_desc')).pack(side=tk.LEFT, padx=5)
        
        # Alphabetical sorting
        alpha_sort_frame = ttk.Frame(sort_frame)
        alpha_sort_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(alpha_sort_frame, text="Alphabetical:").pack(side=tk.LEFT)
        ttk.Button(alpha_sort_frame, text="A-Z", 
                  command=lambda: self.sort_wordlist('alpha_asc')).pack(side=tk.LEFT, padx=5)
        ttk.Button(alpha_sort_frame, text="Z-A", 
                  command=lambda: self.sort_wordlist('alpha_desc')).pack(side=tk.LEFT, padx=5)
        
        # Character type sorting
        char_sort_frame = ttk.Frame(sort_frame)
        char_sort_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(char_sort_frame, text="By Character Type:").pack(side=tk.LEFT)
        ttk.Button(char_sort_frame, text="Letters → Numbers → Special", 
                  command=lambda: self.sort_wordlist('char_type')).pack(side=tk.LEFT, padx=5)
        
        # Duplicate Management
        dup_frame = ttk.LabelFrame(scrollable_frame, text="🚫 Duplicate Management", padding=10)
        dup_frame.pack(fill=tk.X, pady=5, padx=5)
        
        ttk.Button(dup_frame, text="Remove Exact Duplicates", 
                  command=self.remove_exact_duplicates).pack(side=tk.LEFT, padx=5)
        ttk.Button(dup_frame, text="Remove Similar (Fuzzy)", 
                  command=self.remove_similar_duplicates).pack(side=tk.LEFT, padx=5)
        ttk.Button(dup_frame, text="Keep Only Unique Patterns", 
                  command=self.keep_unique_patterns).pack(side=tk.LEFT, padx=5)
        
        # Preview Section
        preview_frame = ttk.LabelFrame(scrollable_frame, text="👁️ Preview", padding=10)
        preview_frame.pack(fill=tk.BOTH, expand=True, pady=5, padx=5)
        
        self.org_preview_text = scrolledtext.ScrolledText(preview_frame, height=10)
        self.org_preview_text.pack(fill=tk.BOTH, expand=True)
        
        # Quick Actions
        actions_frame = ttk.Frame(scrollable_frame)
        actions_frame.pack(fill=tk.X, pady=10)
        
        ttk.Button(actions_frame, text="Apply All Basic Organization", 
                  command=self.apply_basic_organization).pack(side=tk.LEFT, padx=5)
        ttk.Button(actions_frame, text="Export Organized Wordlist", 
                  command=self.export_organized_wordlist).pack(side=tk.LEFT, padx=5)
        
    def setup_advanced_filtering(self, parent):
        """Advanced Filtering Section"""
        container = ttk.Frame(parent)
        container.pack(fill=tk.BOTH, expand=True)
        
        # Create scrollable frame
        canvas = tk.Canvas(container)
        scrollbar = ttk.Scrollbar(container, orient="vertical", command=canvas.yview)
        scrollable_frame = ttk.Frame(canvas)
        
        scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        
        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        
        # Length-Based Filtering
        length_frame = ttk.LabelFrame(scrollable_frame, text="📏 Length-Based Filtering", padding=10)
        length_frame.pack(fill=tk.X, pady=5, padx=5)
        
        # Length range sliders
        length_range_frame = ttk.Frame(length_frame)
        length_range_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(length_range_frame, text="Min Length:").pack(side=tk.LEFT)
        self.min_length_filter = ttk.Spinbox(length_range_frame, from_=1, to=100, width=5)
        self.min_length_filter.set(1)
        self.min_length_filter.pack(side=tk.LEFT, padx=5)
        
        ttk.Label(length_range_frame, text="Max Length:").pack(side=tk.LEFT, padx=(20,0))
        self.max_length_filter = ttk.Spinbox(length_range_frame, from_=1, to=100, width=5)
        self.max_length_filter.set(50)
        self.max_length_filter.pack(side=tk.LEFT, padx=5)
        
        ttk.Button(length_range_frame, text="Apply Length Filter", 
                  command=self.apply_length_filter).pack(side=tk.LEFT, padx=20)
        
        # Preset ranges
        preset_frame = ttk.Frame(length_frame)
        preset_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(preset_frame, text="Preset Ranges:").pack(side=tk.LEFT)
        presets = [("1-8 chars", (1, 8)), ("9-12 chars", (9, 12)), 
                  ("13-16 chars", (13, 16)), ("17-20 chars", (17, 20)), ("21+ chars", (21, 100))]
        
        for text, range_val in presets:
            ttk.Button(preset_frame, text=text, 
                      command=lambda r=range_val: self.apply_preset_range(r)).pack(side=tk.LEFT, padx=2)
        
        # Character Composition Filters
        comp_frame = ttk.LabelFrame(scrollable_frame, text="🔤 Character Composition Filters", padding=10)
        comp_frame.pack(fill=tk.X, pady=5, padx=5)
        
        # Must contain
        must_contain_frame = ttk.Frame(comp_frame)
        must_contain_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(must_contain_frame, text="Must Contain:").pack(side=tk.LEFT)
        self.must_contain_var = tk.StringVar()
        ttk.Entry(must_contain_frame, textvariable=self.must_contain_var, width=20).pack(side=tk.LEFT, padx=5)
        
        # Must NOT contain
        must_not_frame = ttk.Frame(comp_frame)
        must_not_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(must_not_frame, text="Must NOT Contain:").pack(side=tk.LEFT)
        self.must_not_contain_var = tk.StringVar()
        ttk.Entry(must_not_frame, textvariable=self.must_not_contain_var, width=20).pack(side=tk.LEFT, padx=5)
        
        # Character type requirements
        char_req_frame = ttk.Frame(comp_frame)
        char_req_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(char_req_frame, text="Require:").pack(side=tk.LEFT)
        self.require_upper_filter = tk.BooleanVar()
        ttk.Checkbutton(char_req_frame, text="Uppercase", variable=self.require_upper_filter).pack(side=tk.LEFT, padx=5)
        
        self.require_lower_filter = tk.BooleanVar()
        ttk.Checkbutton(char_req_frame, text="Lowercase", variable=self.require_lower_filter).pack(side=tk.LEFT, padx=5)
        
        self.require_digit_filter = tk.BooleanVar()
        ttk.Checkbutton(char_req_frame, text="Digits", variable=self.require_digit_filter).pack(side=tk.LEFT, padx=5)
        
        self.require_special_filter = tk.BooleanVar()
        ttk.Checkbutton(char_req_frame, text="Special", variable=self.require_special_filter).pack(side=tk.LEFT, padx=5)
        
        ttk.Button(comp_frame, text="Apply Composition Filters", 
                  command=self.apply_composition_filters).pack(pady=5)
        
        # Pattern-Based Filtering
        pattern_filter_frame = ttk.LabelFrame(scrollable_frame, text="🎯 Pattern-Based Filtering", padding=10)
        pattern_filter_frame.pack(fill=tk.X, pady=5, padx=5)
        
        # Regex pattern
        regex_frame = ttk.Frame(pattern_filter_frame)
        regex_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(regex_frame, text="Regex Pattern:").pack(side=tk.LEFT)
        self.regex_pattern_var = tk.StringVar()
        ttk.Entry(regex_frame, textvariable=self.regex_pattern_var, width=30).pack(side=tk.LEFT, padx=5)
        ttk.Button(regex_frame, text="Apply Regex", 
                  command=self.apply_regex_filter).pack(side=tk.LEFT, padx=5)
        
        # Starts with/Ends with
        starts_ends_frame = ttk.Frame(pattern_filter_frame)
        starts_ends_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(starts_ends_frame, text="Starts With:").pack(side=tk.LEFT)
        self.starts_with_var = tk.StringVar()
        ttk.Entry(starts_ends_frame, textvariable=self.starts_with_var, width=15).pack(side=tk.LEFT, padx=5)
        
        ttk.Label(starts_ends_frame, text="Ends With:").pack(side=tk.LEFT)
        self.ends_with_var = tk.StringVar()
        ttk.Entry(starts_ends_frame, textvariable=self.ends_with_var, width=15).pack(side=tk.LEFT, padx=5)
        
        ttk.Button(starts_ends_frame, text="Apply Start/End", 
                  command=self.apply_start_end_filter).pack(side=tk.LEFT, padx=20)
        
        # Contains sequence
        sequence_frame = ttk.Frame(pattern_filter_frame)
        sequence_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(sequence_frame, text="Contains Sequence:").pack(side=tk.LEFT)
        self.contains_sequence_var = tk.StringVar()
        ttk.Entry(sequence_frame, textvariable=self.contains_sequence_var, width=20).pack(side=tk.LEFT, padx=5)
        ttk.Button(sequence_frame, text="Apply Sequence Filter", 
                  command=self.apply_sequence_filter).pack(side=tk.LEFT, padx=5)
        
        # Filter Preview
        filter_preview_frame = ttk.LabelFrame(scrollable_frame, text="👁️ Filter Preview", padding=10)
        filter_preview_frame.pack(fill=tk.BOTH, expand=True, pady=5, padx=5)
        
        self.filter_preview_text = scrolledtext.ScrolledText(filter_preview_frame, height=8)
        self.filter_preview_text.pack(fill=tk.BOTH, expand=True)
        
        # Filter Actions
        filter_actions_frame = ttk.Frame(scrollable_frame)
        filter_actions_frame.pack(fill=tk.X, pady=10)
        
        ttk.Button(filter_actions_frame, text="Apply All Filters", 
                  command=self.apply_all_filters).pack(side=tk.LEFT, padx=5)
        ttk.Button(filter_actions_frame, text="Reset All Filters", 
                  command=self.reset_all_filters).pack(side=tk.LEFT, padx=5)
        ttk.Button(filter_actions_frame, text="Export Filtered Wordlist", 
                  command=self.export_filtered_wordlist).pack(side=tk.LEFT, padx=5)
        
    def setup_smart_segmentation(self, parent):
        """Smart Segmentation Section"""
        container = ttk.Frame(parent)
        container.pack(fill=tk.BOTH, expand=True)
        
        # Create scrollable frame
        canvas = tk.Canvas(container)
        scrollbar = ttk.Scrollbar(container, orient="vertical", command=canvas.yview)
        scrollable_frame = ttk.Frame(canvas)
        
        scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        
        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        
        # Automatic Length-Based Splitting
        auto_split_frame = ttk.LabelFrame(scrollable_frame, text="📊 Automatic Length-Based Splitting", padding=10)
        auto_split_frame.pack(fill=tk.X, pady=5, padx=5)
        
        ttk.Label(auto_split_frame, text="Smart Segmentation Options:").pack(anchor=tk.W)
        
        # Predefined ranges
        predefined_frame = ttk.Frame(auto_split_frame)
        predefined_frame.pack(fill=tk.X, pady=10)
        
        self.split_vars = {}
        ranges = [
            ("1-6 characters", (1, 6)),
            ("7-10 characters", (7, 10)),
            ("11-14 characters", (11, 14)),
            ("15-18 characters", (15, 18)),
            ("19+ characters", (19, 100))
        ]
        
        for text, range_val in ranges:
            var = tk.BooleanVar()
            self.split_vars[range_val] = var
            frame = ttk.Frame(predefined_frame)
            frame.pack(fill=tk.X, pady=2)
            ttk.Checkbutton(frame, text=text, variable=var).pack(side=tk.LEFT)
            ttk.Label(frame, text=f"Range: {range_val[0]}-{range_val[1]}").pack(side=tk.LEFT, padx=20)
        
        # Custom ranges
        custom_range_frame = ttk.LabelFrame(auto_split_frame, text="Custom Ranges", padding=10)
        custom_range_frame.pack(fill=tk.X, pady=10)
        
        self.custom_ranges = []
        
        def add_custom_range():
            range_frame = ttk.Frame(custom_range_frame)
            range_frame.pack(fill=tk.X, pady=2)
            
            ttk.Label(range_frame, text="Range:").pack(side=tk.LEFT)
            min_spin = ttk.Spinbox(range_frame, from_=1, to=100, width=5)
            min_spin.set(1)
            min_spin.pack(side=tk.LEFT, padx=5)
            
            ttk.Label(range_frame, text="-").pack(side=tk.LEFT)
            max_spin = ttk.Spinbox(range_frame, from_=1, to=100, width=5)
            max_spin.set(8)
            max_spin.pack(side=tk.LEFT, padx=5)
            
            var = tk.BooleanVar(value=True)
            ttk.Checkbutton(range_frame, text="Include", variable=var).pack(side=tk.LEFT, padx=10)
            
            self.custom_ranges.append((min_spin, max_spin, var, range_frame))
        
        ttk.Button(custom_range_frame, text="Add Custom Range", 
                  command=add_custom_range).pack(anchor=tk.W, pady=5)
        
        # Add initial custom range
        add_custom_range()
        
        # File Naming Convention
        naming_frame = ttk.LabelFrame(scrollable_frame, text="📝 File Naming Convention", padding=10)
        naming_frame.pack(fill=tk.X, pady=5, padx=5)
        
        ttk.Label(naming_frame, text="Naming Pattern:").pack(anchor=tk.W)
        
        naming_pattern_frame = ttk.Frame(naming_frame)
        naming_pattern_frame.pack(fill=tk.X, pady=5)
        
        self.naming_pattern = tk.StringVar(value="[prefix]_[range]_[timestamp]")
        ttk.Entry(naming_pattern_frame, textvariable=self.naming_pattern, width=50).pack(side=tk.LEFT, padx=5)
        
        ttk.Label(naming_pattern_frame, text="Prefix:").pack(side=tk.LEFT, padx=(20,0))
        self.file_prefix = tk.StringVar(value="wordlist")
        ttk.Entry(naming_pattern_frame, textvariable=self.file_prefix, width=15).pack(side=tk.LEFT, padx=5)
        
        # Sequential numbering option
        self.sequential_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(naming_frame, text="Use sequential numbering (wordlist_001.txt, wordlist_002.txt)", 
                       variable=self.sequential_var).pack(anchor=tk.W, pady=5)
        
        # Segmentation Preview
        seg_preview_frame = ttk.LabelFrame(scrollable_frame, text="👁️ Segmentation Preview", padding=10)
        seg_preview_frame.pack(fill=tk.BOTH, expand=True, pady=5, padx=5)
        
        self.seg_preview_text = scrolledtext.ScrolledText(seg_preview_frame, height=8)
        self.seg_preview_text.pack(fill=tk.BOTH, expand=True)
        
        # Segmentation Actions
        seg_actions_frame = ttk.Frame(scrollable_frame)
        seg_actions_frame.pack(fill=tk.X, pady=10)
        
        ttk.Button(seg_actions_frame, text="Preview Segmentation", 
                  command=self.preview_segmentation).pack(side=tk.LEFT, padx=5)
        ttk.Button(seg_actions_frame, text="Execute Segmentation", 
                  command=self.execute_segmentation).pack(side=tk.LEFT, padx=5)
        ttk.Button(seg_actions_frame, text="Export All Segments", 
                  command=self.export_all_segments).pack(side=tk.LEFT, padx=5)
        
    def setup_pattern_analysis(self, parent):
        """Pattern Analysis Section"""
        container = ttk.Frame(parent)
        container.pack(fill=tk.BOTH, expand=True)
        
        # Create scrollable frame
        canvas = tk.Canvas(container)
        scrollbar = ttk.Scrollbar(container, orient="vertical", command=canvas.yview)
        scrollable_frame = ttk.Frame(canvas)
        
        scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        
        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        
        # Common Pattern Detection
        pattern_detection_frame = ttk.LabelFrame(scrollable_frame, text="🔍 Common Pattern Detection", padding=10)
        pattern_detection_frame.pack(fill=tk.X, pady=5, padx=5)
        
        pattern_types_frame = ttk.Frame(pattern_detection_frame)
        pattern_types_frame.pack(fill=tk.X, pady=5)
        
        self.pattern_vars = {}
        pattern_types = [
            ("Dictionary words + numbers", "dict_numbers"),
            ("Leet speak variations", "leet_speak"),
            ("Keyboard walks", "keyboard_walks"),
            ("Date patterns", "date_patterns"),
            ("Common sequences", "common_sequences")
        ]
        
        for text, key in pattern_types:
            var = tk.BooleanVar(value=True)
            self.pattern_vars[key] = var
            ttk.Checkbutton(pattern_types_frame, text=text, variable=var).pack(anchor=tk.W)
        
        ttk.Button(pattern_detection_frame, text="Detect Patterns", 
                  command=self.detect_patterns).pack(pady=5)
        
        # Similarity Grouping
        similarity_frame = ttk.LabelFrame(scrollable_frame, text="🔄 Similarity Grouping", padding=10)
        similarity_frame.pack(fill=tk.X, pady=5, padx=5)
        
        similarity_options_frame = ttk.Frame(similarity_frame)
        similarity_options_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(similarity_options_frame, text="Similarity Threshold:").pack(side=tk.LEFT)
        self.similarity_threshold = ttk.Scale(similarity_options_frame, from_=0.1, to=1.0, orient=tk.HORIZONTAL)
        self.similarity_threshold.set(0.8)
        self.similarity_threshold.pack(side=tk.LEFT, padx=5, fill=tk.X, expand=True)
        
        ttk.Label(similarity_options_frame, text="Group By:").pack(side=tk.LEFT, padx=(20,0))
        self.group_by_var = tk.StringVar(value="base_words")
        ttk.Combobox(similarity_options_frame, textvariable=self.group_by_var,
                    values=["Base Words", "Modification Patterns", "Structure"]).pack(side=tk.LEFT, padx=5)
        
        ttk.Button(similarity_frame, text="Group Similar Passwords", 
                  command=self.group_similar_passwords).pack(pady=5)
        
        # Entropy-Based Organization
        entropy_frame = ttk.LabelFrame(scrollable_frame, text="🛡️ Entropy-Based Organization", padding=10)
        entropy_frame.pack(fill=tk.X, pady=5, padx=5)
        
        entropy_options_frame = ttk.Frame(entropy_frame)
        entropy_options_frame.pack(fill=tk.X, pady=5)
        
        ttk.Button(entropy_options_frame, text="Sort by Password Strength", 
                  command=self.sort_by_strength).pack(side=tk.LEFT, padx=5)
        ttk.Button(entropy_options_frame, text="Group by Entropy Ranges", 
                  command=self.group_by_entropy).pack(side=tk.LEFT, padx=5)
        ttk.Button(entropy_options_frame, text="Identify Weak Patterns", 
                  command=self.identify_weak_patterns).pack(side=tk.LEFT, padx=5)
        
        # Pattern Analysis Results
        pattern_results_frame = ttk.LabelFrame(scrollable_frame, text="📊 Pattern Analysis Results", padding=10)
        pattern_results_frame.pack(fill=tk.BOTH, expand=True, pady=5, padx=5)
        
        self.pattern_results_text = scrolledtext.ScrolledText(pattern_results_frame, height=10)
        self.pattern_results_text.pack(fill=tk.BOTH, expand=True)
        
        # Pattern Actions
        pattern_actions_frame = ttk.Frame(scrollable_frame)
        pattern_actions_frame.pack(fill=tk.X, pady=10)
        
        ttk.Button(pattern_actions_frame, text="Export Pattern Groups", 
                  command=self.export_pattern_groups).pack(side=tk.LEFT, padx=5)
        ttk.Button(pattern_actions_frame, text="Apply Pattern Organization", 
                  command=self.apply_pattern_organization).pack(side=tk.LEFT, padx=5)
        
    def setup_optimization(self, parent):
        """Optimization Section"""
        container = ttk.Frame(parent)
        container.pack(fill=tk.BOTH, expand=True)
        
        # Create scrollable frame
        canvas = tk.Canvas(container)
        scrollbar = ttk.Scrollbar(container, orient="vertical", command=canvas.yview)
        scrollable_frame = ttk.Frame(canvas)
        
        scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        
        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        
        # Compression & Deduplication
        compression_frame = ttk.LabelFrame(scrollable_frame, text="🗜️ Compression & Deduplication", padding=10)
        compression_frame.pack(fill=tk.X, pady=5, padx=5)
        
        compression_options_frame = ttk.Frame(compression_frame)
        compression_options_frame.pack(fill=tk.X, pady=5)
        
        self.advanced_dedup_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(compression_options_frame, text="Advanced Deduplication", 
                       variable=self.advanced_dedup_var).pack(anchor=tk.W)
        
        self.remove_subsets_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(compression_options_frame, text="Remove Subsets", 
                       variable=self.remove_subsets_var).pack(anchor=tk.W)
        
        self.optimize_speed_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(compression_options_frame, text="Optimize for Speed", 
                       variable=self.optimize_speed_var).pack(anchor=tk.W)
        
        self.optimize_coverage_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(compression_options_frame, text="Optimize for Coverage", 
                       variable=self.optimize_coverage_var).pack(anchor=tk.W)
        
        ttk.Button(compression_frame, text="Apply Optimization", 
                  command=self.apply_optimization).pack(pady=5)
        
        # Format Conversion
        format_frame = ttk.LabelFrame(scrollable_frame, text="🔄 Format Conversion", padding=10)
        format_frame.pack(fill=tk.X, pady=5, padx=5)
        
        format_options_frame = ttk.Frame(format_frame)
        format_options_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(format_options_frame, text="Convert To:").pack(side=tk.LEFT)
        self.convert_format_var = tk.StringVar(value="txt")
        formats = [("TXT", "txt"), ("JSON", "json"), ("CSV", "csv"), ("SQLite", "db")]
        
        for text, value in formats:
            ttk.Radiobutton(format_options_frame, text=text, variable=self.convert_format_var, 
                           value=value).pack(side=tk.LEFT, padx=5)
        
        # Encoding options
        encoding_frame = ttk.Frame(format_frame)
        encoding_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(encoding_frame, text="Encoding:").pack(side=tk.LEFT)
        self.encoding_var = tk.StringVar(value="utf-8")
        ttk.Combobox(encoding_frame, textvariable=self.encoding_var,
                    values=["utf-8", "ascii", "latin-1"]).pack(side=tk.LEFT, padx=5)
        
        # Line endings
        ttk.Label(encoding_frame, text="Line Endings:").pack(side=tk.LEFT, padx=(20,0))
        self.line_ending_var = tk.StringVar(value="unix")
        ttk.Combobox(encoding_frame, textvariable=self.line_ending_var,
                    values=["unix (LF)", "windows (CRLF)"]).pack(side=tk.LEFT, padx=5)
        
        ttk.Button(format_frame, text="Convert Format", 
                  command=self.convert_format).pack(pady=5)
        
        # Batch Processing
        batch_org_frame = ttk.LabelFrame(scrollable_frame, text="🔄 Batch Processing", padding=10)
        batch_org_frame.pack(fill=tk.X, pady=5, padx=5)
        
        batch_options_frame = ttk.Frame(batch_org_frame)
        batch_options_frame.pack(fill=tk.X, pady=5)
        
        ttk.Button(batch_options_frame, text="Process Multiple Wordlists", 
                  command=self.batch_process_wordlists).pack(side=tk.LEFT, padx=5)
        ttk.Button(batch_options_frame, text="Merge Wordlists", 
                  command=self.merge_wordlists).pack(side=tk.LEFT, padx=5)
        ttk.Button(batch_options_frame, text="Split Large Wordlist", 
                  command=self.split_large_wordlist).pack(side=tk.LEFT, padx=5)
        
        # Smart Organization Presets
        presets_frame = ttk.LabelFrame(scrollable_frame, text="🎯 Smart Organization Presets", padding=10)
        presets_frame.pack(fill=tk.X, pady=5, padx=5)
        
        presets_options_frame = ttk.Frame(presets_frame)
        presets_options_frame.pack(fill=tk.X, pady=5)
        
        self.preset_var = tk.StringVar(value="pentesting")
        presets = [
            ("Pentesting Ready", "pentesting"),
            ("Research Mode", "research"),
            ("Storage Optimized", "storage"),
            ("Custom Profile", "custom")
        ]
        
        for text, value in presets:
            ttk.Radiobutton(presets_options_frame, text=text, variable=self.preset_var, 
                           value=value).pack(anchor=tk.W)
        
        ttk.Button(presets_frame, text="Apply Preset", 
                  command=self.apply_organization_preset).pack(side=tk.LEFT, padx=5)
        ttk.Button(presets_frame, text="Save Custom Profile", 
                  command=self.save_custom_profile).pack(side=tk.LEFT, padx=5)
        
        # One-Click Optimization
        one_click_frame = ttk.Frame(scrollable_frame)
        one_click_frame.pack(fill=tk.X, pady=10)
        
        ttk.Button(one_click_frame, text="🚀 Smart Organize (One-Click)", 
                  command=self.smart_organize, style="Accent.TButton").pack(side=tk.LEFT, padx=5)
        ttk.Button(one_click_frame, text="Optimize for Speed", 
                  command=lambda: self.optimize_for("speed")).pack(side=tk.LEFT, padx=5)
        ttk.Button(one_click_frame, text="Optimize for Coverage", 
                  command=lambda: self.optimize_for("coverage")).pack(side=tk.LEFT, padx=5)
        
    def setup_organizer_statistics(self, parent):
        """Statistics & Analytics Dashboard"""
        container = ttk.Frame(parent)
        container.pack(fill=tk.BOTH, expand=True)
        
        # Create scrollable frame
        canvas = tk.Canvas(container)
        scrollbar = ttk.Scrollbar(container, orient="vertical", command=canvas.yview)
        scrollable_frame = ttk.Frame(canvas)
        
        scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        
        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        
        # Comprehensive Statistics
        stats_frame = ttk.LabelFrame(scrollable_frame, text="📈 Comprehensive Statistics", padding=10)
        stats_frame.pack(fill=tk.X, pady=5, padx=5)
        
        self.org_detailed_stats_text = scrolledtext.ScrolledText(stats_frame, height=12)
        self.org_detailed_stats_text.pack(fill=tk.BOTH, expand=True)
        
        # Pattern Frequency Analysis
        pattern_freq_frame = ttk.LabelFrame(scrollable_frame, text="🔤 Pattern Frequency Analysis", padding=10)
        pattern_freq_frame.pack(fill=tk.X, pady=5, padx=5)
        
        pattern_freq_options_frame = ttk.Frame(pattern_freq_frame)
        pattern_freq_options_frame.pack(fill=tk.X, pady=5)
        
        ttk.Button(pattern_freq_options_frame, text="Analyze Common Base Words", 
                  command=self.analyze_base_words).pack(side=tk.LEFT, padx=5)
        ttk.Button(pattern_freq_options_frame, text="Analyze Suffixes/Prefixes", 
                  command=self.analyze_affixes).pack(side=tk.LEFT, padx=5)
        ttk.Button(pattern_freq_options_frame, text="Character Frequency", 
                  command=self.analyze_character_frequency).pack(side=tk.LEFT, padx=5)
        
        self.pattern_freq_text = scrolledtext.ScrolledText(pattern_freq_frame, height=8)
        self.pattern_freq_text.pack(fill=tk.BOTH, expand=True)
        
        # Export & Reporting
        export_frame = ttk.LabelFrame(scrollable_frame, text="📤 Export & Reporting", padding=10)
        export_frame.pack(fill=tk.X, pady=5, padx=5)
        
        export_options_frame = ttk.Frame(export_frame)
        export_options_frame.pack(fill=tk.X, pady=5)
        
        ttk.Button(export_options_frame, text="Generate Comprehensive Report", 
                  command=self.generate_comprehensive_report).pack(side=tk.LEFT, padx=5)
        ttk.Button(export_options_frame, text="Export Statistics", 
                  command=self.export_statistics).pack(side=tk.LEFT, padx=5)
        ttk.Button(export_options_frame, text="Save Analysis Summary", 
                  command=self.save_analysis_summary).pack(side=tk.LEFT, padx=5)
        
        # Update statistics initially
        self.update_organizer_statistics()

    # ========== WORDLIST ORGANIZER METHODS ==========

    def load_organization_profiles(self):
        """Load organization profiles from file"""
        profile_file = "organization_profiles.json"
        if os.path.exists(profile_file):
            try:
                with open(profile_file, 'r') as f:
                    self.organization_profiles = json.load(f)
            except:
                self.organization_profiles = {
                    "pentesting": {
                        "name": "Pentesting Ready",
                        "sort_by": "length_asc",
                        "filters": {"min_length": 1, "max_length": 50},
                        "deduplication": True,
                        "optimization": "speed"
                    },
                    "research": {
                        "name": "Research Mode", 
                        "sort_by": "alpha_asc",
                        "filters": {},
                        "deduplication": False,
                        "optimization": "coverage"
                    },
                    "storage": {
                        "name": "Storage Optimized",
                        "sort_by": "length_asc", 
                        "filters": {"min_length": 8, "max_length": 30},
                        "deduplication": True,
                        "optimization": "compression"
                    }
                }

    def load_wordlist_for_org(self):
        """Load wordlist file for organization"""
        filename = filedialog.askopenfilename(
            title="Load Wordlist for Organization",
            filetypes=[("Text files", "*.txt"), ("All files", "*.*")]
        )
        
        if filename:
            try:
                with open(filename, 'r', encoding='utf-8', errors='ignore') as f:
                    self.current_wordlist = [line.strip() for line in f if line.strip()]
                
                self.update_organizer_statistics()
                self.update_org_preview()
                messagebox.showinfo("Success", f"Loaded {len(self.current_wordlist):,} passwords from {filename}")
                
            except Exception as e:
                messagebox.showerror("Error", f"Failed to load wordlist: {str(e)}")

    def use_generated_wordlist(self):
        """Use the currently generated wordlist"""
        if hasattr(self, 'preview_text'):
            content = self.preview_text.get("1.0", tk.END).strip()
            if content:
                self.current_wordlist = [line.strip() for line in content.split('\n') if line.strip()]
                self.update_organizer_statistics()
                self.update_org_preview()
                messagebox.showinfo("Success", f"Using {len(self.current_wordlist):,} passwords from generated wordlist")
            else:
                messagebox.showwarning("Warning", "No generated wordlist available")
        else:
            messagebox.showwarning("Warning", "No generated wordlist available")

    def clear_current_wordlist(self):
        """Clear the current wordlist"""
        self.current_wordlist = []
        self.update_organizer_statistics()
        self.update_org_preview()
        messagebox.showinfo("Cleared", "Current wordlist cleared")

    def update_organizer_statistics(self):
        """Update organizer statistics display"""
        if not self.current_wordlist:
            self.org_stats_label.config(text="No wordlist loaded")
            self.org_detailed_stats_text.delete(1.0, tk.END)
            return
        
        total = len(self.current_wordlist)
        if total == 0:
            self.org_stats_label.config(text="Wordlist is empty")
            return
        
        # Basic stats
        lengths = [len(pwd) for pwd in self.current_wordlist]
        min_len = min(lengths)
        max_len = max(lengths)
        avg_len = sum(lengths) / total
        
        stats_text = f"Total: {total:,} | Min: {min_len} | Max: {max_len} | Avg: {avg_len:.1f}"
        self.org_stats_label.config(text=stats_text)
        
        # Detailed statistics
        detailed_stats = self.calculate_detailed_statistics()
        self.org_detailed_stats_text.delete(1.0, tk.END)
        self.org_detailed_stats_text.insert(1.0, detailed_stats)

    def calculate_detailed_statistics(self):
        """Calculate detailed statistics for the current wordlist"""
        if not self.current_wordlist:
            return "No wordlist loaded"
        
        total = len(self.current_wordlist)
        lengths = [len(pwd) for pwd in self.current_wordlist]
        
        # Length distribution
        length_bins = {
            "1-4": 0, "5-8": 0, "9-12": 0, 
            "13-16": 0, "17-20": 0, "21+": 0
        }
        
        for length in lengths:
            if length <= 4:
                length_bins["1-4"] += 1
            elif length <= 8:
                length_bins["5-8"] += 1
            elif length <= 12:
                length_bins["9-12"] += 1
            elif length <= 16:
                length_bins["13-16"] += 1
            elif length <= 20:
                length_bins["17-20"] += 1
            else:
                length_bins["21+"] += 1
        
        # Character composition
        pure_lower = 0
        pure_upper = 0
        mixed_case = 0
        with_numbers = 0
        with_special = 0
        
        for pwd in self.current_wordlist:
            if pwd.islower():
                pure_lower += 1
            elif pwd.isupper():
                pure_upper += 1
            elif any(c.islower() for c in pwd) and any(c.isupper() for c in pwd):
                mixed_case += 1
            
            if any(c.isdigit() for c in pwd):
                with_numbers += 1
            if any(not c.isalnum() for c in pwd):
                with_special += 1
        
        # Build statistics report
        report = [
            "=== WORDLIST STATISTICS ===",
            f"Total entries: {total:,}",
            f"Shortest password: {min(lengths)} character(s)",
            f"Longest password: {max(lengths)} character(s)",
            f"Average length: {sum(lengths)/total:.2f} characters",
            "",
            "LENGTH DISTRIBUTION:",
        ]
        
        for bin_name, count in length_bins.items():
            percentage = (count / total) * 100
            report.append(f"{bin_name} chars: {count:,} ({percentage:.1f}%)")
        
        report.extend([
            "",
            "CHARACTER COMPOSITION:",
            f"Pure lowercase: {pure_lower:,} ({pure_lower/total*100:.1f}%)",
            f"Pure uppercase: {pure_upper:,} ({pure_upper/total*100:.1f}%)", 
            f"Mixed case: {mixed_case:,} ({mixed_case/total*100:.1f}%)",
            f"With numbers: {with_numbers:,} ({with_numbers/total*100:.1f}%)",
            f"With special chars: {with_special:,} ({with_special/total*100:.1f}%)",
        ])
        
        return "\n".join(report)

    def update_org_preview(self):
        """Update organizer preview"""
        if not self.current_wordlist:
            self.org_preview_text.delete(1.0, tk.END)
            self.org_preview_text.insert(1.0, "No wordlist loaded")
            return
        
        preview_count = min(50, len(self.current_wordlist))
        preview_text = "\n".join(self.current_wordlist[:preview_count])
        
        if len(self.current_wordlist) > preview_count:
            preview_text += f"\n... and {len(self.current_wordlist) - preview_count} more"
        
        self.org_preview_text.delete(1.0, tk.END)
        self.org_preview_text.insert(1.0, preview_text)

    # ========== BASIC ORGANIZATION METHODS ==========

    def sort_wordlist(self, sort_type):
        """Sort the current wordlist"""
        if not self.current_wordlist:
            messagebox.showwarning("Warning", "No wordlist to sort")
            return
        
        try:
            if sort_type == 'length_asc':
                self.current_wordlist.sort(key=len)
            elif sort_type == 'length_desc':
                self.current_wordlist.sort(key=len, reverse=True)
            elif sort_type == 'alpha_asc':
                self.current_wordlist.sort()
            elif sort_type == 'alpha_desc':
                self.current_wordlist.sort(reverse=True)
            elif sort_type == 'char_type':
                self.current_wordlist.sort(key=self.char_type_key)
            
            self.update_org_preview()
            self.update_organizer_statistics()
            messagebox.showinfo("Success", f"Wordlist sorted by {sort_type}")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to sort wordlist: {str(e)}")

    def char_type_key(self, password):
        """Key function for character type sorting"""
        if password.isalpha():
            if password.islower():
                return (0, password)  # Pure lowercase first
            elif password.isupper():
                return (1, password)  # Pure uppercase second
            else:
                return (2, password)  # Mixed case third
        elif password.isdigit():
            return (3, password)  # Numbers fourth
        else:
            return (4, password)  # Special chars last

    def remove_exact_duplicates(self):
        """Remove exact duplicates from wordlist"""
        if not self.current_wordlist:
            messagebox.showwarning("Warning", "No wordlist to process")
            return
        
        original_count = len(self.current_wordlist)
        self.current_wordlist = list(set(self.current_wordlist))
        removed_count = original_count - len(self.current_wordlist)
        
        self.update_org_preview()
        self.update_organizer_statistics()
        messagebox.showinfo("Success", f"Removed {removed_count} exact duplicates")

    def remove_similar_duplicates(self):
        """Remove similar duplicates using fuzzy matching"""
        if not self.current_wordlist:
            messagebox.showwarning("Warning", "No wordlist to process")
            return
        
        try:
            original_count = len(self.current_wordlist)
            threshold = 0.8  # Similarity threshold
            
            # Simple fuzzy deduplication
            unique_passwords = []
            for pwd in self.current_wordlist:
                is_similar = False
                for unique_pwd in unique_passwords:
                    if self.similarity(pwd, unique_pwd) > threshold:
                        is_similar = True
                        break
                if not is_similar:
                    unique_passwords.append(pwd)
            
            self.current_wordlist = unique_passwords
            removed_count = original_count - len(self.current_wordlist)
            
            self.update_org_preview()
            self.update_organizer_statistics()
            messagebox.showinfo("Success", f"Removed {removed_count} similar duplicates (threshold: {threshold})")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to remove similar duplicates: {str(e)}")

    def similarity(self, a, b):
        """Calculate similarity between two strings"""
        return SequenceMatcher(None, a, b).ratio()

    def keep_unique_patterns(self):
        """Keep only passwords with unique patterns"""
        if not self.current_wordlist:
            messagebox.showwarning("Warning", "No wordlist to process")
            return
        
        try:
            original_count = len(self.current_wordlist)
            
            # Group by pattern characteristics
            pattern_groups = defaultdict(list)
            for pwd in self.current_wordlist:
                # Create a pattern signature
                signature = self.create_pattern_signature(pwd)
                pattern_groups[signature].append(pwd)
            
            # Keep only one from each pattern group
            unique_passwords = []
            for group in pattern_groups.values():
                unique_passwords.append(group[0])  # Keep the first one
            
            self.current_wordlist = unique_passwords
            removed_count = original_count - len(self.current_wordlist)
            
            self.update_org_preview()
            self.update_organizer_statistics()
            messagebox.showinfo("Success", f"Kept {len(unique_passwords)} unique patterns, removed {removed_count} duplicates")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to keep unique patterns: {str(e)}")

    def create_pattern_signature(self, password):
        """Create a pattern signature for a password"""
        # Convert to pattern: lowercase letters -> 'a', uppercase -> 'A', digits -> '1', special -> '*'
        signature = []
        for char in password:
            if char.islower():
                signature.append('a')
            elif char.isupper():
                signature.append('A')
            elif char.isdigit():
                signature.append('1')
            else:
                signature.append('*')
        return ''.join(signature)

    def apply_basic_organization(self):
        """Apply all basic organization steps"""
        if not self.current_wordlist:
            messagebox.showwarning("Warning", "No wordlist to organize")
            return
        
        try:
            # Remove duplicates
            self.current_wordlist = list(set(self.current_wordlist))
            
            # Sort by length (ascending)
            self.current_wordlist.sort(key=len)
            
            self.update_org_preview()
            self.update_organizer_statistics()
            messagebox.showinfo("Success", "Applied basic organization: deduplication + length sorting")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to apply basic organization: {str(e)}")

    def export_organized_wordlist(self):
        """Export the organized wordlist"""
        if not self.current_wordlist:
            messagebox.showwarning("Warning", "No wordlist to export")
            return
        
        filename = filedialog.asksaveasfilename(
            title="Export Organized Wordlist",
            defaultextension=".txt",
            filetypes=[("Text files", "*.txt"), ("All files", "*.*")]
        )
        
        if filename:
            try:
                with open(filename, 'w', encoding='utf-8') as f:
                    for password in self.current_wordlist:
                        f.write(password + '\n')
                
                messagebox.showinfo("Success", f"Exported {len(self.current_wordlist):,} passwords to {filename}")
                
            except Exception as e:
                messagebox.showerror("Error", f"Failed to export wordlist: {str(e)}")

    # ========== ADVANCED FILTERING METHODS ==========

    def apply_length_filter(self):
        """Apply length-based filtering"""
        if not self.current_wordlist:
            messagebox.showwarning("Warning", "No wordlist to filter")
            return
        
        try:
            min_len = int(self.min_length_filter.get())
            max_len = int(self.max_length_filter.get())
            
            filtered = [pwd for pwd in self.current_wordlist if min_len <= len(pwd) <= max_len]
            removed_count = len(self.current_wordlist) - len(filtered)
            
            self.current_wordlist = filtered
            self.update_org_preview()
            self.update_organizer_statistics()
            
            messagebox.showinfo("Success", f"Applied length filter: {min_len}-{max_len} chars. Removed {removed_count} passwords.")
            
        except ValueError:
            messagebox.showerror("Error", "Please enter valid numbers for min and max length")

    def apply_preset_range(self, range_val):
        """Apply preset length range"""
        self.min_length_filter.set(range_val[0])
        self.max_length_filter.set(range_val[1])
        self.apply_length_filter()

    def apply_composition_filters(self):
        """Apply character composition filters"""
        if not self.current_wordlist:
            messagebox.showwarning("Warning", "No wordlist to filter")
            return
        
        try:
            filtered = self.current_wordlist.copy()
            
            # Must contain
            must_contain = self.must_contain_var.get().strip()
            if must_contain:
                filtered = [pwd for pwd in filtered if must_contain in pwd]
            
            # Must NOT contain
            must_not_contain = self.must_not_contain_var.get().strip()
            if must_not_contain:
                filtered = [pwd for pwd in filtered if must_not_contain not in pwd]
            
            # Character type requirements
            if self.require_upper_filter.get():
                filtered = [pwd for pwd in filtered if any(c.isupper() for c in pwd)]
            
            if self.require_lower_filter.get():
                filtered = [pwd for pwd in filtered if any(c.islower() for c in pwd)]
            
            if self.require_digit_filter.get():
                filtered = [pwd for pwd in filtered if any(c.isdigit() for c in pwd)]
            
            if self.require_special_filter.get():
                filtered = [pwd for pwd in filtered if any(not c.isalnum() for c in pwd)]
            
            removed_count = len(self.current_wordlist) - len(filtered)
            self.current_wordlist = filtered
            
            self.update_org_preview()
            self.update_organizer_statistics()
            messagebox.showinfo("Success", f"Applied composition filters. Removed {removed_count} passwords.")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to apply composition filters: {str(e)}")

    def apply_regex_filter(self):
        """Apply regex pattern filter"""
        if not self.current_wordlist:
            messagebox.showwarning("Warning", "No wordlist to filter")
            return
        
        pattern = self.regex_pattern_var.get().strip()
        if not pattern:
            messagebox.showwarning("Warning", "Please enter a regex pattern")
            return
        
        try:
            regex = re.compile(pattern)
            filtered = [pwd for pwd in self.current_wordlist if regex.search(pwd)]
            removed_count = len(self.current_wordlist) - len(filtered)
            
            self.current_wordlist = filtered
            self.update_org_preview()
            self.update_organizer_statistics()
            messagebox.showinfo("Success", f"Applied regex filter. Removed {removed_count} passwords.")
            
        except re.error as e:
            messagebox.showerror("Error", f"Invalid regex pattern: {str(e)}")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to apply regex filter: {str(e)}")

    def apply_start_end_filter(self):
        """Apply starts with/ends with filters"""
        if not self.current_wordlist:
            messagebox.showwarning("Warning", "No wordlist to filter")
            return
        
        starts_with = self.starts_with_var.get().strip()
        ends_with = self.ends_with_var.get().strip()
        
        if not starts_with and not ends_with:
            messagebox.showwarning("Warning", "Please enter at least one filter")
            return
        
        try:
            filtered = self.current_wordlist.copy()
            
            if starts_with:
                filtered = [pwd for pwd in filtered if pwd.startswith(starts_with)]
            
            if ends_with:
                filtered = [pwd for pwd in filtered if pwd.endswith(ends_with)]
            
            removed_count = len(self.current_wordlist) - len(filtered)
            self.current_wordlist = filtered
            
            self.update_org_preview()
            self.update_organizer_statistics()
            messagebox.showinfo("Success", f"Applied start/end filters. Removed {removed_count} passwords.")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to apply start/end filters: {str(e)}")

    def apply_sequence_filter(self):
        """Apply contains sequence filter"""
        if not self.current_wordlist:
            messagebox.showwarning("Warning", "No wordlist to filter")
            return
        
        sequence = self.contains_sequence_var.get().strip()
        if not sequence:
            messagebox.showwarning("Warning", "Please enter a sequence to filter")
            return
        
        try:
            filtered = [pwd for pwd in self.current_wordlist if sequence in pwd]
            removed_count = len(self.current_wordlist) - len(filtered)
            
            self.current_wordlist = filtered
            self.update_org_preview()
            self.update_organizer_statistics()
            messagebox.showinfo("Success", f"Applied sequence filter. Removed {removed_count} passwords.")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to apply sequence filter: {str(e)}")

    def apply_all_filters(self):
        """Apply all active filters"""
        # This would combine all filter methods
        # For now, just show a message
        messagebox.showinfo("Info", "This would apply all active filters. Implement based on your specific needs.")

    def reset_all_filters(self):
        """Reset all filters to default"""
        self.min_length_filter.set(1)
        self.max_length_filter.set(50)
        self.must_contain_var.set("")
        self.must_not_contain_var.set("")
        self.require_upper_filter.set(False)
        self.require_lower_filter.set(False)
        self.require_digit_filter.set(False)
        self.require_special_filter.set(False)
        self.regex_pattern_var.set("")
        self.starts_with_var.set("")
        self.ends_with_var.set("")
        self.contains_sequence_var.set("")
        
        messagebox.showinfo("Success", "All filters reset to default values")

    def export_filtered_wordlist(self):
        """Export the filtered wordlist"""
        self.export_organized_wordlist()  # Reuse the same method

    # ========== SMART SEGMENTATION METHODS ==========

    def preview_segmentation(self):
        """Preview the segmentation results"""
        if not self.current_wordlist:
            messagebox.showwarning("Warning", "No wordlist to segment")
            return
        
        try:
            segments = {}
            
            # Predefined ranges
            for range_val, var in self.split_vars.items():
                if var.get():
                    min_len, max_len = range_val
                    segments[f"{min_len}-{max_len}"] = [
                        pwd for pwd in self.current_wordlist 
                        if min_len <= len(pwd) <= max_len
                    ]
            
            # Custom ranges
            for min_spin, max_spin, var, _ in self.custom_ranges:
                if var.get():
                    try:
                        min_len = int(min_spin.get())
                        max_len = int(max_spin.get())
                        range_name = f"custom_{min_len}-{max_len}"
                        segments[range_name] = [
                            pwd for pwd in self.current_wordlist 
                            if min_len <= len(pwd) <= max_len
                        ]
                    except ValueError:
                        continue
            
            # Build preview
            preview_text = "Segmentation Preview:\n\n"
            total_in_segments = 0
            
            for range_name, segment_list in segments.items():
                preview_text += f"{range_name} chars: {len(segment_list):,} passwords\n"
                total_in_segments += len(segment_list)
            
            preview_text += f"\nTotal in segments: {total_in_segments:,}\n"
            preview_text += f"Original total: {len(self.current_wordlist):,}\n"
            preview_text += f"Not in any segment: {len(self.current_wordlist) - total_in_segments:,}"
            
            self.seg_preview_text.delete(1.0, tk.END)
            self.seg_preview_text.insert(1.0, preview_text)
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to preview segmentation: {str(e)}")

    def execute_segmentation(self):
        """Execute the segmentation and store results"""
        if not self.current_wordlist:
            messagebox.showwarning("Warning", "No wordlist to segment")
            return
        
        try:
            self.organized_wordlists.clear()
            
            # Predefined ranges
            for range_val, var in self.split_vars.items():
                if var.get():
                    min_len, max_len = range_val
                    range_name = f"{min_len}-{max_len}"
                    self.organized_wordlists[range_name] = [
                        pwd for pwd in self.current_wordlist 
                        if min_len <= len(pwd) <= max_len
                    ]
            
            # Custom ranges
            for min_spin, max_spin, var, _ in self.custom_ranges:
                if var.get():
                    try:
                        min_len = int(min_spin.get())
                        max_len = int(max_spin.get())
                        range_name = f"custom_{min_len}-{max_len}"
                        self.organized_wordlists[range_name] = [
                            pwd for pwd in self.current_wordlist 
                            if min_len <= len(pwd) <= max_len
                        ]
                    except ValueError:
                        continue
            
            # Show results
            total_segmented = sum(len(lst) for lst in self.organized_wordlists.values())
            messagebox.showinfo("Success", 
                              f"Segmentation completed!\n"
                              f"Created {len(self.organized_wordlists)} segments\n"
                              f"Total passwords segmented: {total_segmented:,}")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to execute segmentation: {str(e)}")

    def export_all_segments(self):
        """Export all segments to files"""
        if not self.organized_wordlists:
            messagebox.showwarning("Warning", "No segments to export. Please execute segmentation first.")
            return
        
        output_dir = filedialog.askdirectory(title="Select Output Directory for Segments")
        if not output_dir:
            return
        
        try:
            exported_count = 0
            prefix = self.file_prefix.get().strip() or "wordlist"
            
            for segment_name, segment_list in self.organized_wordlists.items():
                if segment_list:  # Only export non-empty segments
                    if self.sequential_var.get():
                        filename = f"{prefix}_{exported_count+1:03d}.txt"
                    else:
                        filename = f"{prefix}_{segment_name}.txt"
                    
                    filepath = os.path.join(output_dir, filename)
                    
                    with open(filepath, 'w', encoding='utf-8') as f:
                        for password in segment_list:
                            f.write(password + '\n')
                    
                    exported_count += 1
            
            messagebox.showinfo("Success", f"Exported {exported_count} segments to {output_dir}")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to export segments: {str(e)}")

    # ========== PATTERN ANALYSIS METHODS ==========

    def detect_patterns(self):
        """Detect common password patterns"""
        if not self.current_wordlist:
            messagebox.showwarning("Warning", "No wordlist to analyze")
            return
        
        try:
            patterns = {
                "dict_numbers": [],
                "leet_speak": [],
                "keyboard_walks": [],
                "date_patterns": [],
                "common_sequences": []
            }
            
            for pwd in self.current_wordlist:
                pwd_lower = pwd.lower()
                
                # Dictionary words + numbers
                if any(word in pwd_lower for word in ["password", "admin", "user", "login"]) and any(c.isdigit() for c in pwd):
                    patterns["dict_numbers"].append(pwd)
                
                # Leet speak detection (basic)
                leet_chars = {'@', '3', '1', '0', '7', '5', '$'}
                if any(char in pwd for char in leet_chars):
                    patterns["leet_speak"].append(pwd)
                
                # Keyboard walks
                keyboard_patterns = ["qwerty", "asdfgh", "zxcvbn", "123456"]
                if any(pattern in pwd_lower for pattern in keyboard_patterns):
                    patterns["keyboard_walks"].append(pwd)
                
                # Date patterns (basic)
                date_patterns = ["1900", "2000", "2020", "2021", "2022", "2023", "2024"]
                if any(pattern in pwd for pattern in date_patterns):
                    patterns["date_patterns"].append(pwd)
                
                # Common sequences
                sequences = ["123", "abc", "111", "000", "1234", "12345"]
                if any(seq in pwd for seq in sequences):
                    patterns["common_sequences"].append(pwd)
            
            # Build results
            results = "Pattern Analysis Results:\n\n"
            for pattern_type, pattern_list in patterns.items():
                results += f"{pattern_type}: {len(pattern_list):,} passwords\n"
            
            results += "\nSample passwords for each pattern:\n"
            for pattern_type, pattern_list in patterns.items():
                if pattern_list:
                    results += f"\n{pattern_type}:\n"
                    sample = pattern_list[:5]  # Show first 5
                    for pwd in sample:
                        results += f"  {pwd}\n"
            
            self.pattern_results_text.delete(1.0, tk.END)
            self.pattern_results_text.insert(1.0, results)
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to detect patterns: {str(e)}")

    def group_similar_passwords(self):
        """Group similar passwords together"""
        if not self.current_wordlist:
            messagebox.showwarning("Warning", "No wordlist to group")
            return
        
        try:
            threshold = self.similarity_threshold.get()
            groups = []
            used = set()
            
            for i, pwd1 in enumerate(self.current_wordlist):
                if i in used:
                    continue
                
                group = [pwd1]
                used.add(i)
                
                for j, pwd2 in enumerate(self.current_wordlist[i+1:], i+1):
                    if j in used:
                        continue
                    
                    if self.similarity(pwd1, pwd2) > threshold:
                        group.append(pwd2)
                        used.add(j)
                
                if len(group) > 1:  # Only show groups with multiple members
                    groups.append(group)
            
            # Display results
            results = f"Similar Password Groups (threshold: {threshold:.1f}):\n\n"
            results += f"Found {len(groups)} groups with similar passwords\n\n"
            
            for i, group in enumerate(groups[:10]):  # Show first 10 groups
                results += f"Group {i+1} ({len(group)} passwords):\n"
                for pwd in group[:5]:  # Show first 5 in each group
                    results += f"  {pwd}\n"
                if len(group) > 5:
                    results += f"  ... and {len(group)-5} more\n"
                results += "\n"
            
            self.pattern_results_text.delete(1.0, tk.END)
            self.pattern_results_text.insert(1.0, results)
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to group similar passwords: {str(e)}")

    def sort_by_strength(self):
        """Sort passwords by strength"""
        if not self.current_wordlist:
            messagebox.showwarning("Warning", "No wordlist to sort")
            return
        
        try:
            # Sort by multiple strength factors
            self.current_wordlist.sort(key=lambda p: (
                -len(p),  # Longer passwords first (negative for descending)
                -len(set(p)),  # More unique characters
                -sum(1 for c in p if not c.isalnum()),  # More special chars
                -sum(1 for c in p if c.isdigit()),  # More digits
                -sum(1 for c in p if c.isupper())  # More uppercase
            ))
            
            self.update_org_preview()
            self.update_organizer_statistics()
            messagebox.showinfo("Success", "Passwords sorted by strength")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to sort by strength: {str(e)}")

    def group_by_entropy(self):
        """Group passwords by entropy ranges"""
        if not self.current_wordlist:
            messagebox.showwarning("Warning", "No wordlist to group")
            return
        
        try:
            entropy_groups = {
                "Very Low (0-20)": [],
                "Low (21-40)": [],
                "Medium (41-60)": [],
                "High (61-80)": [],
                "Very High (81+)": []
            }
            
            for pwd in self.current_wordlist:
                entropy = self.calculate_entropy(pwd)
                if entropy <= 20:
                    entropy_groups["Very Low (0-20)"].append(pwd)
                elif entropy <= 40:
                    entropy_groups["Low (21-40)"].append(pwd)
                elif entropy <= 60:
                    entropy_groups["Medium (41-60)"].append(pwd)
                elif entropy <= 80:
                    entropy_groups["High (61-80)"].append(pwd)
                else:
                    entropy_groups["Very High (81+)"].append(pwd)
            
            # Store for later use
            self.organized_wordlists.update(entropy_groups)
            
            # Display results
            results = "Entropy-Based Groups:\n\n"
            for group_name, group_list in entropy_groups.items():
                results += f"{group_name}: {len(group_list):,} passwords\n"
            
            self.pattern_results_text.delete(1.0, tk.END)
            self.pattern_results_text.insert(1.0, results)
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to group by entropy: {str(e)}")

    def identify_weak_patterns(self):
        """Identify weak password patterns"""
        if not self.current_wordlist:
            messagebox.showwarning("Warning", "No wordlist to analyze")
            return
        
        try:
            weak_patterns = {
                "Too Short (<8 chars)": [],
                "Common Words": [],
                "Sequential Chars": [],
                "Repeated Chars": [],
                "No Character Variety": []
            }
            
            common_words = {"password", "admin", "123456", "qwerty", "letmein", "welcome", "monkey"}
            sequential_patterns = ["123", "234", "345", "456", "567", "678", "789", "abc", "bcd", "cde"]
            
            for pwd in self.current_wordlist:
                pwd_lower = pwd.lower()
                
                if len(pwd) < 8:
                    weak_patterns["Too Short (<8 chars)"].append(pwd)
                
                if any(word in pwd_lower for word in common_words):
                    weak_patterns["Common Words"].append(pwd)
                
                if any(seq in pwd_lower for seq in sequential_patterns):
                    weak_patterns["Sequential Chars"].append(pwd)
                
                if re.search(r'(.)\1{2,}', pwd):  # 3 or more repeated chars
                    weak_patterns["Repeated Chars"].append(pwd)
                
                # Check character variety
                char_types = 0
                if any(c.islower() for c in pwd):
                    char_types += 1
                if any(c.isupper() for c in pwd):
                    char_types += 1
                if any(c.isdigit() for c in pwd):
                    char_types += 1
                if any(not c.isalnum() for c in pwd):
                    char_types += 1
                
                if char_types < 2 and len(pwd) >= 8:
                    weak_patterns["No Character Variety"].append(pwd)
            
            # Display results
            results = "Weak Pattern Analysis:\n\n"
            total_weak = 0
            for pattern_type, pattern_list in weak_patterns.items():
                results += f"{pattern_type}: {len(pattern_list):,} passwords\n"
                total_weak += len(pattern_list)
            
            results += f"\nTotal passwords with weak patterns: {total_weak:,}\n"
            results += f"Percentage: {(total_weak/len(self.current_wordlist))*100:.1f}%"
            
            self.pattern_results_text.delete(1.0, tk.END)
            self.pattern_results_text.insert(1.0, results)
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to identify weak patterns: {str(e)}")

    def export_pattern_groups(self):
        """Export pattern analysis groups"""
        if not self.organized_wordlists:
            messagebox.showwarning("Warning", "No pattern groups to export")
            return
        
        self.export_all_segments()  # Reuse the same method

    def apply_pattern_organization(self):
        """Apply pattern-based organization"""
        messagebox.showinfo("Info", "Pattern organization would be applied here")

    # ========== OPTIMIZATION METHODS ==========

    def apply_optimization(self):
        """Apply optimization settings"""
        if not self.current_wordlist:
            messagebox.showwarning("Warning", "No wordlist to optimize")
            return
        
        try:
            original_count = len(self.current_wordlist)
            
            # Advanced deduplication
            if self.advanced_dedup_var.get():
                self.current_wordlist = list(set(self.current_wordlist))
            
            # Remove subsets (if a word is contained in another word)
            if self.remove_subsets_var.get():
                self.current_wordlist = [pwd for pwd in self.current_wordlist 
                                       if not any(pwd in other and pwd != other 
                                                for other in self.current_wordlist)]
            
            # Optimize for speed (shorter passwords first)
            if self.optimize_speed_var.get():
                self.current_wordlist.sort(key=len)
            
            # Optimize for coverage (more variety)
            if self.optimize_coverage_var.get():
                # Sort by uniqueness of character composition
                self.current_wordlist.sort(key=lambda p: -len(set(p)))
            
            final_count = len(self.current_wordlist)
            removed_count = original_count - final_count
            
            self.update_org_preview()
            self.update_organizer_statistics()
            messagebox.showinfo("Success", 
                              f"Optimization applied!\n"
                              f"Original: {original_count:,}\n"
                              f"Final: {final_count:,}\n"
                              f"Removed: {removed_count:,}")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to apply optimization: {str(e)}")

    def convert_format(self):
        """Convert wordlist to different format"""
        if not self.current_wordlist:
            messagebox.showwarning("Warning", "No wordlist to convert")
            return
        
        filename = filedialog.asksaveasfilename(
            title=f"Save As {self.convert_format_var.get().upper()}",
            defaultextension=f".{self.convert_format_var.get()}",
            filetypes=[(f"{self.convert_format_var.get().upper()} files", f"*.{self.convert_format_var.get()}")]
        )
        
        if filename:
            try:
                format_type = self.convert_format_var.get()
                encoding = self.encoding_var.get()
                line_ending = "\n" if self.line_ending_var.get() == "unix (LF)" else "\r\n"
                
                if format_type == "txt":
                    with open(filename, 'w', encoding=encoding) as f:
                        for password in self.current_wordlist:
                            f.write(password + line_ending)
                
                elif format_type == "json":
                    with open(filename, 'w', encoding=encoding) as f:
                        json.dump(self.current_wordlist, f, indent=2)
                
                elif format_type == "csv":
                    with open(filename, 'w', encoding=encoding, newline='') as f:
                        writer = csv.writer(f)
                        writer.writerow(["Password"])
                        for password in self.current_wordlist:
                            writer.writerow([password])
                
                elif format_type == "db":
                    conn = sqlite3.connect(filename)
                    cursor = conn.cursor()
                    cursor.execute('''
                        CREATE TABLE passwords (
                            id INTEGER PRIMARY KEY AUTOINCREMENT,
                            password TEXT UNIQUE,
                            length INTEGER,
                            entropy REAL
                        )
                    ''')
                    for password in self.current_wordlist:
                        cursor.execute(
                            "INSERT OR IGNORE INTO passwords (password, length, entropy) VALUES (?, ?, ?)",
                            (password, len(password), self.calculate_entropy(password))
                        )
                    conn.commit()
                    conn.close()
                
                messagebox.showinfo("Success", f"Wordlist converted to {format_type.upper()} format")
                
            except Exception as e:
                messagebox.showerror("Error", f"Failed to convert format: {str(e)}")

    def batch_process_wordlists(self):
        """Process multiple wordlists in batch"""
        files = filedialog.askopenfilenames(
            title="Select Wordlists for Batch Processing",
            filetypes=[("Text files", "*.txt"), ("All files", "*.*")]
        )
        
        if files:
            output_dir = filedialog.askdirectory(title="Select Output Directory")
            if output_dir:
                # This would process each file with the current organization settings
                messagebox.showinfo("Info", f"Would process {len(files)} files with current organization settings")

    def merge_wordlists(self):
        """Merge multiple wordlists"""
        files = filedialog.askopenfilenames(
            title="Select Wordlists to Merge",
            filetypes=[("Text files", "*.txt"), ("All files", "*.*")]
        )
        
        if len(files) < 2:
            messagebox.showwarning("Warning", "Please select at least 2 wordlists to merge")
            return
        
        try:
            merged = set()
            for file in files:
                with open(file, 'r', encoding='utf-8', errors='ignore') as f:
                    merged.update(line.strip() for line in f if line.strip())
            
            self.current_wordlist = list(merged)
            self.update_org_preview()
            self.update_organizer_statistics()
            messagebox.showinfo("Success", f"Merged {len(files)} wordlists into {len(merged):,} unique passwords")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to merge wordlists: {str(e)}")

    def split_large_wordlist(self):
        """Split a large wordlist into smaller chunks"""
        if not self.current_wordlist:
            messagebox.showwarning("Warning", "No wordlist to split")
            return
        
        chunk_size = tk.simpledialog.askinteger("Split Wordlist", "Enter chunk size:", initialvalue=100000)
        if not chunk_size:
            return
        
        output_dir = filedialog.askdirectory(title="Select Output Directory for Chunks")
        if not output_dir:
            return
        
        try:
            total_chunks = (len(self.current_wordlist) + chunk_size - 1) // chunk_size
            
            for i in range(total_chunks):
                start_idx = i * chunk_size
                end_idx = min((i + 1) * chunk_size, len(self.current_wordlist))
                chunk = self.current_wordlist[start_idx:end_idx]
                
                filename = os.path.join(output_dir, f"chunk_{i+1:03d}.txt")
                with open(filename, 'w', encoding='utf-8') as f:
                    for password in chunk:
                        f.write(password + '\n')
            
            messagebox.showinfo("Success", f"Split wordlist into {total_chunks} chunks of {chunk_size} passwords each")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to split wordlist: {str(e)}")

    def apply_organization_preset(self):
        """Apply organization preset"""
        preset = self.preset_var.get()
        
        if preset == "pentesting":
            # Apply pentesting preset
            self.min_length_filter.set(1)
            self.max_length_filter.set(50)
            self.apply_length_filter()
            self.remove_exact_duplicates()
            self.sort_wordlist('length_asc')
            
        elif preset == "research":
            # Apply research preset
            self.sort_wordlist('alpha_asc')
            
        elif preset == "storage":
            # Apply storage preset
            self.min_length_filter.set(8)
            self.max_length_filter.set(30)
            self.apply_length_filter()
            self.remove_exact_duplicates()
            self.sort_wordlist('length_asc')
            
        elif preset == "custom":
            # Custom preset would load from saved profiles
            messagebox.showinfo("Info", "Custom preset would be loaded from saved profiles")
        
        messagebox.showinfo("Success", f"Applied {preset} organization preset")

    def save_custom_profile(self):
        """Save current settings as custom profile"""
        name = tk.simpledialog.askstring("Save Profile", "Enter profile name:")
        if name:
            # Save current organization settings
            self.organization_profiles[name] = {
                "name": name,
                "filters": {
                    "min_length": self.min_length_filter.get(),
                    "max_length": self.max_length_filter.get(),
                    # Add other filter settings...
                },
                "sort_type": "custom",  # You would track the current sort type
                "optimization": "custom"
            }
            messagebox.showinfo("Success", f"Profile '{name}' saved")

    def smart_organize(self):
        """One-click smart organization"""
        if not self.current_wordlist:
            messagebox.showwarning("Warning", "No wordlist to organize")
            return
        
        try:
            # Comprehensive organization pipeline
            original_count = len(self.current_wordlist)
            
            # Step 1: Deduplication
            self.current_wordlist = list(set(self.current_wordlist))
            
            # Step 2: Remove obviously weak passwords
            self.current_wordlist = [pwd for pwd in self.current_wordlist if len(pwd) >= 4]
            
            # Step 3: Sort by multiple criteria
            self.current_wordlist.sort(key=lambda p: (
                len(p),  # Length primary
                p  # Alphabetical secondary
            ))
            
            final_count = len(self.current_wordlist)
            removed_count = original_count - final_count
            
            self.update_org_preview()
            self.update_organizer_statistics()
            messagebox.showinfo("Smart Organization Complete", 
                              f"Original: {original_count:,} passwords\n"
                              f"Final: {final_count:,} passwords\n"
                              f"Removed: {removed_count:,} passwords\n"
                              f"Reduction: {(removed_count/original_count)*100:.1f}%")
            
        except Exception as e:
            messagebox.showerror("Error", f"Smart organization failed: {str(e)}")

    def optimize_for(self, optimization_type):
        """Optimize for specific use case"""
        if not self.current_wordlist:
            messagebox.showwarning("Warning", "No wordlist to optimize")
            return
        
        if optimization_type == "speed":
            # Optimize for cracking speed (shorter passwords first)
            self.current_wordlist.sort(key=len)
            messagebox.showinfo("Success", "Optimized for speed (shorter passwords first)")
        
        elif optimization_type == "coverage":
            # Optimize for coverage (more variety)
            self.current_wordlist.sort(key=lambda p: -len(set(p)))
            messagebox.showinfo("Success", "Optimized for coverage (more character variety)")
        
        self.update_org_preview()

    # ========== STATISTICS & ANALYTICS METHODS ==========

    def analyze_base_words(self):
        """Analyze common base words in passwords"""
        if not self.current_wordlist:
            messagebox.showwarning("Warning", "No wordlist to analyze")
            return
        
        try:
            # Common base words (simplified analysis)
            base_words = Counter()
            common_words = {"password", "admin", "user", "login", "welcome", "letmein", "master", "root"}
            
            for pwd in self.current_wordlist:
                pwd_lower = pwd.lower()
                for word in common_words:
                    if word in pwd_lower:
                        base_words[word] += 1
            
            results = "Common Base Words Analysis:\n\n"
            for word, count in base_words.most_common(20):
                percentage = (count / len(self.current_wordlist)) * 100
                results += f"{word}: {count:,} ({percentage:.1f}%)\n"
            
            self.pattern_freq_text.delete(1.0, tk.END)
            self.pattern_freq_text.insert(1.0, results)
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to analyze base words: {str(e)}")

    def analyze_affixes(self):
        """Analyze common suffixes and prefixes"""
        if not self.current_wordlist:
            messagebox.showwarning("Warning", "No wordlist to analyze")
            return
        
        try:
            suffixes = Counter()
            prefixes = Counter()
            
            common_affixes = {"123", "!", "!!", "1", "12", "1234", "2020", "2021", "2022", "2023", "2024"}
            
            for pwd in self.current_wordlist:
                for affix in common_affixes:
                    if pwd.endswith(affix):
                        suffixes[affix] += 1
                    if pwd.startswith(affix):
                        prefixes[affix] += 1
            
            results = "Common Affixes Analysis:\n\n"
            results += "SUFFIXES:\n"
            for affix, count in suffixes.most_common(10):
                percentage = (count / len(self.current_wordlist)) * 100
                results += f"  {affix}: {count:,} ({percentage:.1f}%)\n"
            
            results += "\nPREFIXES:\n"
            for affix, count in prefixes.most_common(10):
                percentage = (count / len(self.current_wordlist)) * 100
                results += f"  {affix}: {count:,} ({percentage:.1f}%)\n"
            
            self.pattern_freq_text.delete(1.0, tk.END)
            self.pattern_freq_text.insert(1.0, results)
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to analyze affixes: {str(e)}")

    def analyze_character_frequency(self):
        """Analyze character frequency in passwords"""
        if not self.current_wordlist:
            messagebox.showwarning("Warning", "No wordlist to analyze")
            return
        
        try:
            all_chars = ''.join(self.current_wordlist)
            char_freq = Counter(all_chars)
            
            results = "Character Frequency Analysis (Top 50):\n\n"
            for char, count in char_freq.most_common(50):
                percentage = (count / len(all_chars)) * 100
                # Escape special characters for display
                display_char = repr(char)[1:-1] if char in ['\n', '\t', '\r'] else char
                results += f"'{display_char}': {count:,} ({percentage:.2f}%)\n"
            
            self.pattern_freq_text.delete(1.0, tk.END)
            self.pattern_freq_text.insert(1.0, results)
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to analyze character frequency: {str(e)}")

    def generate_comprehensive_report(self):
        """Generate a comprehensive organization report"""
        if not self.current_wordlist:
            messagebox.showwarning("Warning", "No wordlist to report on")
            return
        
        filename = filedialog.asksaveasfilename(
            title="Save Comprehensive Report",
            defaultextension=".txt",
            filetypes=[("Text files", "*.txt"), ("All files", "*.*")]
        )
        
        if filename:
            try:
                report = self.calculate_detailed_statistics()
                report += "\n\n" + "="*50 + "\n"
                report += "ORGANIZATION SUMMARY\n"
                report += "="*50 + "\n\n"
                
                # Add organization details
                report += f"Total organized segments: {len(self.organized_wordlists)}\n"
                for segment_name, segment_list in self.organized_wordlists.items():
                    report += f"{segment_name}: {len(segment_list):,} passwords\n"
                
                with open(filename, 'w', encoding='utf-8') as f:
                    f.write(report)
                
                messagebox.showinfo("Success", f"Comprehensive report saved to {filename}")
                
            except Exception as e:
                messagebox.showerror("Error", f"Failed to generate report: {str(e)}")

    def export_statistics(self):
        """Export statistics to file"""
        self.generate_comprehensive_report()  # Reuse the same method

    def save_analysis_summary(self):
        """Save analysis summary"""
        self.generate_comprehensive_report()  # Reuse the same method

    # ========== THEME MANAGEMENT ==========
    
    def apply_theme(self, theme_name):
        """Apply theme to all widgets"""
        if theme_name not in self.themes:
            return
            
        theme = self.themes[theme_name]
        self.current_theme = theme_name
        
        # Configure root window
        self.root.configure(bg=theme['bg'])
        
        # Configure ttk style
        self.style.configure('.', 
                           background=theme['bg'],
                           foreground=theme['fg'],
                           fieldbackground=theme['text_bg'])
        
        self.style.configure('TLabel', 
                           background=theme['bg'],
                           foreground=theme['fg'])
        
        self.style.configure('TFrame', 
                           background=theme['bg'])
        
        self.style.configure('TLabelframe', 
                           background=theme['bg'],
                           foreground=theme['fg'])
        
        self.style.configure('TLabelframe.Label', 
                           background=theme['bg'],
                           foreground=theme['fg'])
        
        self.style.configure('TButton',
                           background=theme['button_bg'],
                           foreground=theme['button_fg'])
        
        self.style.configure('TEntry',
                           fieldbackground=theme['text_bg'],
                           foreground=theme['text_fg'])
        
        self.style.configure('TScrollbar',
                           background=theme['button_bg'],
                           troughcolor=theme['secondary_bg'])
        
        # Configure treeview
        self.style.configure('Treeview',
                           background=theme['tree_bg'],
                           foreground=theme['tree_fg'],
                           fieldbackground=theme['tree_bg'])
        
        self.style.configure('Treeview.Heading',
                           background=theme['button_bg'],
                           foreground=theme['button_fg'])
        
        # Configure status frame
        self.status_frame.configure(bg=theme['secondary_bg'])
        self.status_label.configure(bg=theme['secondary_bg'], fg=theme['fg'])
        
        # Configure text widgets
        text_widgets = [
            (self.preview_text, theme['text_bg'], theme['text_fg']),
            (self.stats_text, theme['text_bg'], theme['text_fg']),
            (self.pattern_text, theme['text_bg'], theme['text_fg']),
            (self.charset_preview_text, theme['text_bg'], theme['text_fg']),
            (self.org_preview_text, theme['text_bg'], theme['text_fg']),
            (self.filter_preview_text, theme['text_bg'], theme['text_fg']),
            (self.seg_preview_text, theme['text_bg'], theme['text_fg']),
            (self.pattern_results_text, theme['text_bg'], theme['text_fg']),
            (self.org_detailed_stats_text, theme['text_bg'], theme['text_fg']),
            (self.pattern_freq_text, theme['text_bg'], theme['text_fg'])
        ]
        
        for widget, bg, fg in text_widgets:
            if widget:
                widget.configure(bg=bg, fg=fg, insertbackground=fg)
        
        # Update all child widgets
        self.update_widget_colors(self.root, theme)
    
    def update_widget_colors(self, parent, theme):
        """Recursively update widget colors"""
        try:
            for child in parent.winfo_children():
                if isinstance(child, tk.Text) or isinstance(child, tk.Entry):
                    child.configure(bg=theme['text_bg'], fg=theme['text_fg'],
                                  insertbackground=theme['text_fg'])
                elif isinstance(child, tk.Listbox):
                    child.configure(bg=theme['text_bg'], fg=theme['text_fg'])
                elif isinstance(child, tk.Frame) and not isinstance(child, ttk.Frame):
                    child.configure(bg=theme['bg'])
                elif isinstance(child, tk.Label) and not isinstance(child, ttk.Label):
                    child.configure(bg=theme['bg'], fg=theme['fg'])
                
                # Recursively update children
                self.update_widget_colors(child, theme)
        except tk.TclError:
            pass
    
    def apply_theme_from_settings(self):
        """Apply theme from settings selection"""
        theme = self.theme_var.get()
        self.apply_theme(theme)
        messagebox.showinfo("Success", f"Theme changed to {self.themes[theme]['name']}")

    # ========== CHARACTER SET MANAGEMENT ==========
    
    def update_charset_preview(self):
        """Update character set preview"""
        charset = self.get_active_charset()
        preview_text = f"Active Character Set ({len(charset)} characters):\n{charset}"
        
        self.charset_preview_text.delete(1.0, tk.END)
        self.charset_preview_text.insert(1.0, preview_text)
    
    def get_active_charset(self):
        """Get combined character set based on selections"""
        charset = ""
        
        for key, var in self.charset_vars.items():
            if var.get():
                charset += self.character_sets[key]
        
        # Add custom characters
        custom_chars = self.custom_chars_var.get().strip()
        if custom_chars:
            charset += custom_chars
        
        # Remove excluded characters
        exclude_chars = self.exclude_chars_var.get().strip()
        if exclude_chars:
            charset = ''.join(c for c in charset if c not in exclude_chars)
        
        # Remove duplicates and return
        return ''.join(sorted(set(charset)))

    # ========== CORE FUNCTIONALITY ==========
    
    def add_word(self):
        word = self.word_entry.get().strip()
        repetition = self.rep_entry.get().strip()
        
        if not word:
            messagebox.showwarning("Warning", "Please enter a word")
            return
        
        try:
            repetition = int(repetition)
            if repetition < 1:
                raise ValueError("Repetition must be at least 1")
        except ValueError:
            messagebox.showwarning("Warning", "Please enter a valid number for repetitions")
            return
        
        if word not in self.words:
            self.words.append(word)
            self.repetitions[word] = repetition
            
            item_id = self.tree.insert('', tk.END, values=(word, repetition))
            self.word_to_item[word] = item_id
            
            self.word_entry.delete(0, tk.END)
            self.update_stats()
    
    def remove_word(self):
        selected_items = self.tree.selection()
        if not selected_items:
            messagebox.showwarning("Warning", "Please select a word to remove")
            return
        
        for item in selected_items:
            item_values = self.tree.item(item, 'values')
            if item_values:
                word = item_values[0]
                
                if word in self.words:
                    self.words.remove(word)
                if word in self.repetitions:
                    del self.repetitions[word]
                if word in self.word_to_item:
                    del self.word_to_item[word]
                
                self.tree.delete(item)
        
        self.update_stats()
    
    def clear_all(self):
        if not self.words:
            return
            
        if messagebox.askyesno("Confirm", "Are you sure you want to clear all words?"):
            self.words.clear()
            self.repetitions.clear()
            self.word_to_item.clear()
            for item in self.tree.get_children():
                self.tree.delete(item)
            self.update_stats()
    
    def edit_word(self):
        selected_items = self.tree.selection()
        if not selected_items:
            messagebox.showwarning("Warning", "Please select a word to edit")
            return
        
        item = selected_items[0]
        current_values = self.tree.item(item, 'values')
        
        # Create edit dialog
        self.create_edit_dialog(item, current_values)
    
    def create_edit_dialog(self, item, values):
        dialog = tk.Toplevel(self.root)
        dialog.title("Edit Word")
        dialog.geometry("300x150")
        dialog.transient(self.root)
        dialog.grab_set()
        
        # Apply theme to dialog
        theme = self.themes[self.current_theme]
        dialog.configure(bg=theme['bg'])
        
        ttk.Label(dialog, text="Word:").pack(pady=5)
        word_entry = ttk.Entry(dialog, width=30)
        word_entry.insert(0, values[0])
        word_entry.pack(pady=5)
        
        ttk.Label(dialog, text="Max Repetitions:").pack(pady=5)
        rep_entry = ttk.Entry(dialog, width=10)
        rep_entry.insert(0, values[1])
        rep_entry.pack(pady=5)
        
        def save_changes():
            new_word = word_entry.get().strip()
            new_rep = rep_entry.get().strip()
            
            if not new_word:
                messagebox.showwarning("Warning", "Word cannot be empty")
                return
            
            try:
                new_rep = int(new_rep)
                if new_rep < 1:
                    raise ValueError
            except ValueError:
                messagebox.showwarning("Warning", "Please enter a valid number")
                return
            
            # Update data
            old_word = values[0]
            if old_word in self.words:
                self.words.remove(old_word)
            if old_word in self.repetitions:
                del self.repetitions[old_word]
            if old_word in self.word_to_item:
                del self.word_to_item[old_word]
            
            self.words.append(new_word)
            self.repetitions[new_word] = new_rep
            self.word_to_item[new_word] = item
            
            self.tree.item(item, values=(new_word, new_rep))
            self.update_stats()
            dialog.destroy()
        
        ttk.Button(dialog, text="Save", command=save_changes).pack(pady=10)
    
    def update_stats(self):
        word_count = len(self.words)
        total_repetitions = sum(self.repetitions.values())
        estimated = self.estimate_combinations()
        self.stats_label.config(text=f"Words: {word_count} | Total Positions: {total_repetitions} | Estimated: {estimated:,}")
    
    def estimate_combinations(self):
        if not self.words:
            return 0
        
        total_positions = sum(self.repetitions.values())
        
        if self.permutations_var.get():
            # Estimate permutations based on total positions
            estimate = 0
            for length in range(1, min(total_positions, 10) + 1):
                estimate += math.factorial(total_positions) // math.factorial(total_positions - length)
        else:
            # Estimate combinations
            estimate = 2 ** min(total_positions, 20) - 1
        
        # Apply multipliers for rules
        multipliers = 1
        if self.case_var.get():
            multipliers *= 4  # lower, UPPER, Title, Mixed
        if self.leet_var.get():
            multipliers *= 2  # rough estimate
        
        # Apply character set multiplier
        charset_size = len(self.get_active_charset())
        if charset_size > 0:
            multipliers *= min(charset_size, 10)  # Cap the multiplier
        
        return min(estimate * multipliers, 10**12)  # Cap at 1 trillion

    # ========== ULTIMATE GENERATION ENGINE ==========
    
    def generate_combinations(self):
        """Ultimate combination generation with all advanced features"""
        all_combinations = set()
        
        if not self.words:
            return []
        
        # Base combinations from words
        base_combinations = self.generate_base_combinations()
        all_combinations.update(base_combinations)
        
        # Apply advanced rules
        rule_combinations = self.apply_advanced_rules(base_combinations)
        all_combinations.update(rule_combinations)
        
        # Apply character-based generation
        char_combinations = self.apply_character_generation(all_combinations)
        all_combinations.update(char_combinations)
        
        # Apply leet speak
        if self.leet_var.get():
            leet_combinations = self.apply_leet_speak(all_combinations)
            all_combinations.update(leet_combinations)
        
        # Apply patterns
        patterns = self.get_patterns()
        if patterns:
            pattern_combinations = self.apply_patterns(all_combinations, patterns)
            all_combinations.update(pattern_combinations)
        
        # Apply strength filtering
        all_combinations = self.apply_strength_filter(all_combinations)
        
        # Convert to list and sort
        result = list(all_combinations)
        if self.sort_var.get():
            result.sort(key=lambda x: (len(x), x))
        
        # Update preview
        preview_text = "\n".join(result[:50])  # Show first 50
        if len(result) > 50:
            preview_text += f"\n... and {len(result) - 50} more"
        
        self.preview_text.delete(1.0, tk.END)
        self.preview_text.insert(1.0, preview_text)
        
        return result
    
    def generate_base_combinations(self):
        """Generate base combinations using SMART approach for large word sets"""
        combinations = set()
        
        if self.permutations_var.get():
            # SMART PERMUTATIONS APPROACH - Generate meaningful combinations
            total_positions = sum(self.repetitions.values())
            
            # Create expanded word pool with repetitions
            expanded_words = []
            for word, count in self.repetitions.items():
                expanded_words.extend([word] * count)
            
            # Strategy: Generate combinations in smart batches
            combinations.update(self.generate_single_words())
            combinations.update(self.generate_word_pairs())
            combinations.update(self.generate_triples())
            combinations.update(self.generate_sequential_combinations())
            combinations.update(self.generate_max_length_combinations())
            
        else:
            # Sequential combinations
            combinations.update(self.generate_sequential_combinations())
        
        return combinations
    
    def generate_single_words(self):
        """Generate all single words with their repetitions"""
        combinations = set()
        for word in self.words:
            combinations.add(word)
            if self.case_var.get():
                self.add_case_variations(word, combinations)
        return combinations
    
    def generate_word_pairs(self):
        """Generate all possible 2-word combinations"""
        combinations = set()
        
        # Generate pairs from all words considering repetitions
        for word1 in self.words:
            for word2 in self.words:
                # Check if we can use these words based on their repetition limits
                if (self.repetitions[word1] >= 1 and self.repetitions[word2] >= 1 and 
                    word1 != word2):
                    
                    # Generate the pair
                    pair = word1 + word2
                    combinations.add(pair)
                    
                    if self.case_var.get():
                        self.add_case_variations(pair, combinations)
        
        return combinations
    
    def generate_triples(self):
        """Generate all possible 3-word combinations"""
        combinations = set()
        
        for word1 in self.words:
            for word2 in self.words:
                for word3 in self.words:
                    # Check repetition limits
                    words_used = [word1, word2, word3]
                    word_count = {}
                    valid = True
                    
                    for word in words_used:
                        word_count[word] = word_count.get(word, 0) + 1
                        if word_count[word] > self.repetitions[word]:
                            valid = False
                            break
                    
                    if valid:
                        triple = word1 + word2 + word3
                        combinations.add(triple)
                        
                        if self.case_var.get():
                            self.add_case_variations(triple, combinations)
        
        return combinations
    
    def generate_sequential_combinations(self):
        """Generate sequential combinations of increasing lengths"""
        combinations = set()
        total_positions = sum(self.repetitions.values())
        
        # Generate combinations of different sizes
        for size in range(1, min(len(self.words), 6) + 1):
            for combo in itertools.combinations(self.words, size):
                # Generate permutations for this combination considering repetitions
                self.generate_smart_permutations_for_combo(combo, combinations)
        
        return combinations
    
    def generate_smart_permutations_for_combo(self, combo, combinations):
        """Generate smart permutations for a word combination"""
        # Create word pool based on repetition limits
        word_pool = []
        for word in combo:
            word_pool.extend([word] * self.repetitions[word])
        
        # Generate permutations for different lengths
        max_length = min(len(word_pool), 15)  # Increased limit
        
        for length in range(1, max_length + 1):
            count = 0
            # Use sample of permutations to avoid explosion
            for perm in self.sample_permutations(word_pool, length, 1000):
                password = ''.join(perm)
                combinations.add(password)
                
                if self.case_var.get():
                    self.add_case_variations(password, combinations)
                
                count += 1
                if count >= 1000:  # Limit per length
                    break
    
    def sample_permutations(self, word_pool, length, sample_size):
        """Generate a sample of permutations without generating all"""
        seen = set()
        attempts = 0
        max_attempts = sample_size * 10
        
        while len(seen) < sample_size and attempts < max_attempts:
            attempts += 1
            # Create a random permutation
            if len(word_pool) >= length:
                sample = random.sample(word_pool, length)
                # Check if this sample respects repetition limits
                if self.is_valid_permutation(sample):
                    tuple_sample = tuple(sample)
                    if tuple_sample not in seen:
                        seen.add(tuple_sample)
                        yield sample
    
    def generate_max_length_combinations(self):
        """Generate combinations that use maximum repetitions"""
        combinations = set()
        
        # Create a list that uses maximum repetitions of each word
        max_usage_words = []
        for word, count in self.repetitions.items():
            max_usage_words.extend([word] * count)
        
        # Generate some maximum length combinations
        if len(max_usage_words) > 0:
            # Shuffle and create some max combinations
            for _ in range(min(100, math.factorial(len(max_usage_words)))):
                random.shuffle(max_usage_words)
                max_combo = ''.join(max_usage_words)
                combinations.add(max_combo)
                
                if self.case_var.get():
                    self.add_case_variations(max_combo, combinations)
        
        return combinations
    
    def is_valid_permutation(self, permutation):
        """Check if a permutation respects individual word repetition limits"""
        word_count = {}
        for word in permutation:
            word_count[word] = word_count.get(word, 0) + 1
            if word_count[word] > self.repetitions[word]:
                return False
        return True
    
    def apply_advanced_rules(self, base_combinations):
        """Apply all advanced rule-based transformations"""
        result = set()
        
        for password in list(base_combinations)[:2000]:  # Increased processing limit
            variations = set()
            variations.add(password)
            
            # Common suffixes and prefixes
            if self.rule_vars.get("suffixes") and self.rule_vars["suffixes"].get():
                for pattern in self.patterns_db["number_sequences"][:15]:
                    variations.add(password + pattern)
                    variations.add(pattern + password)
            
            if self.rule_vars.get("prefixes") and self.rule_vars["prefixes"].get():
                for pattern in self.patterns_db["number_sequences"][:15]:
                    variations.add(pattern + password)
                    variations.add(password + pattern)
            
            # Keyboard walks
            if self.rule_vars.get("keyboard_walk") and self.rule_vars["keyboard_walk"].get():
                for walk in list(self.patterns_db["keyboard_walks"].values())[:5]:
                    variations.add(password + walk[:4])
                    variations.add(walk[:4] + password)
            
            # Number sequences
            if self.rule_vars.get("number_sequences") and self.rule_vars["number_sequences"].get():
                for seq in self.patterns_db["number_sequences"][:20]:
                    variations.add(password + seq)
                    variations.add(seq + password)
            
            # Date patterns
            if self.rule_vars.get("date_patterns") and self.rule_vars["date_patterns"].get():
                for date in self.patterns_db["date_formats"][:15]:
                    variations.add(password + date)
                    variations.add(date + password)
            
            # Common fragments
            if self.rule_vars.get("common_fragments") and self.rule_vars["common_fragments"].get():
                for fragment in self.patterns_db["common_fragments"][:15]:
                    variations.add(password + fragment)
                    variations.add(fragment + password)
            
            # Social engineering patterns
            if self.rule_vars.get("social_patterns") and self.rule_vars["social_patterns"].get():
                for category in self.patterns_db["social_patterns"].values():
                    for word in category[:5]:
                        variations.add(password + word)
                        variations.add(word + password)
            
            # Company patterns
            if self.rule_vars.get("company_patterns") and self.rule_vars["company_patterns"].get():
                for category in self.patterns_db["company_patterns"].values():
                    for word in category[:5]:
                        variations.add(password + word)
                        variations.add(word + password)
            
            # Basic transformations
            if self.rule_vars.get("capitalize") and self.rule_vars["capitalize"].get():
                variations.add(password.capitalize())
                variations.add(password.upper())
                variations.add(password.lower())
                # Mixed case variations
                if len(password) > 1:
                    variations.add(password[0].upper() + password[1:].lower())
            
            if self.rule_vars.get("reverse") and self.rule_vars["reverse"].get():
                variations.add(password[::-1])
            
            if self.rule_vars.get("duplicate") and self.rule_vars["duplicate"].get():
                variations.add(password * 2)
                variations.add(password * 3)
                if len(password) < 20:
                    variations.add(password * 4)
            
            result.update(variations)
        
        return result
    
    def apply_character_generation(self, combinations):
        """Apply character-based password generation"""
        result = set()
        charset = self.get_active_charset()
        
        if not charset:
            return result
        
        # Add character-based variations to existing passwords
        for password in list(combinations)[:1000]:
            # Add character prefixes/suffixes
            for char in charset[:15]:  # Use more chars
                result.add(char + password)
                result.add(password + char)
                result.add(char + password + char)
            
            # Replace characters with charset options
            if len(password) > 0:
                for i in range(min(5, len(password))):
                    for char in charset[:8]:
                        new_pass = password[:i] + char + password[i+1:]
                        result.add(new_pass)
        
        return result
    
    def apply_leet_speak(self, combinations):
        """Apply leet speak substitutions based on selected level"""
        result = set()
        level = self.leet_level_var.get()
        
        if level not in self.leet_levels:
            return result
        
        leet_map = self.leet_levels[level]
        
        for password in list(combinations)[:2000]:
            # Simple leet substitution
            leet_password = ""
            for char in password:
                if char.lower() in leet_map:
                    substitutions = leet_map[char.lower()]
                    if isinstance(substitutions, list):
                        leet_password += random.choice(substitutions)
                    else:
                        leet_password += substitutions
                else:
                    leet_password += char
            result.add(leet_password)
            
            # Also add partial leet substitutions
            if len(password) > 3:
                partial_leet = ""
                for char in password:
                    if char.lower() in leet_map and random.random() > 0.5:
                        substitutions = leet_map[char.lower()]
                        if isinstance(substitutions, list):
                            partial_leet += random.choice(substitutions)
                        else:
                            partial_leet += substitutions
                    else:
                        partial_leet += char
                result.add(partial_leet)
        
        return result
    
    def apply_patterns(self, combinations, patterns):
        """Apply custom patterns"""
        result = set()
        
        for password in list(combinations)[:1000]:
            for pattern in patterns[:20]:
                result.add(password + pattern)
                result.add(pattern + password)
                # Also try inserting pattern in the middle
                if len(password) > 2:
                    mid = len(password) // 2
                    result.add(password[:mid] + pattern + password[mid:])
        
        return result
    
    def apply_strength_filter(self, combinations):
        """Filter combinations based on strength requirements"""
        result = set()
        
        try:
            min_len = int(self.min_length_var.get())
            max_len = int(self.max_length_var.get())
        except ValueError:
            min_len = 1
            max_len = 100  # Increased max length
        
        for password in combinations:
            # Length filter
            if not (min_len <= len(password) <= max_len):
                continue
            
            # Character type requirements
            if self.require_upper_var.get() and not any(c.isupper() for c in password):
                continue
            if self.require_lower_var.get() and not any(c.islower() for c in password):
                continue
            if self.require_digit_var.get() and not any(c.isdigit() for c in password):
                continue
            if self.require_special_var.get() and not any(not c.isalnum() for c in password):
                continue
            
            result.add(password)
        
        return result
    
    def add_case_variations(self, password, combinations):
        """Add case variations"""
        if password:
            combinations.add(password.lower())
            combinations.add(password.upper())
            combinations.add(password.title())
            # Mixed case variations
            if len(password) > 1:
                combinations.add(password[0].upper() + password[1:].lower())
                # Random mixed case (a few samples)
                for _ in range(3):
                    mixed = ''.join(random.choice([c.upper(), c.lower()]) for c in password)
                    combinations.add(mixed)
    
    def get_patterns(self):
        """Get patterns from pattern text area"""
        pattern_text = self.pattern_text.get("1.0", tk.END).strip()
        if pattern_text:
            return [p.strip() for p in pattern_text.split('\n') if p.strip()]
        return []

    # ========== FILE OPERATIONS ==========
    
    def import_from_text(self):
        filename = filedialog.askopenfilename(
            title="Import from Text File",
            filetypes=[("Text files", "*.txt"), ("All files", "*.*")]
        )
        
        if filename:
            try:
                with open(filename, 'r', encoding='utf-8', errors='ignore') as f:
                    words = [line.strip() for line in f if line.strip()]
                
                added_count = 0
                for word in words[:1000]:  # Limit import
                    if word not in self.words:
                        self.words.append(word)
                        self.repetitions[word] = 2  # Default repetition
                        item_id = self.tree.insert('', tk.END, values=(word, 2))
                        self.word_to_item[word] = item_id
                        added_count += 1
                
                self.update_stats()
                messagebox.showinfo("Success", f"Imported {added_count} words from {filename}")
                
            except Exception as e:
                messagebox.showerror("Error", f"Failed to import file: {str(e)}")
    
    def import_from_csv(self):
        filename = filedialog.askopenfilename(
            title="Import from CSV",
            filetypes=[("CSV files", "*.csv"), ("All files", "*.*")]
        )
        
        if filename:
            try:
                df = pd.read_csv(filename)
                # Assume first column contains words
                words = df.iloc[:, 0].dropna().astype(str).tolist()
                
                added_count = 0
                for word in words[:1000]:  # Limit import
                    if word not in self.words:
                        self.words.append(word)
                        self.repetitions[word] = 2
                        item_id = self.tree.insert('', tk.END, values=(word, 2))
                        self.word_to_item[word] = item_id
                        added_count += 1
                
                self.update_stats()
                messagebox.showinfo("Success", f"Imported {added_count} words from CSV")
                
            except Exception as e:
                messagebox.showerror("Error", f"Failed to import CSV: {str(e)}")
    
    def paste_from_clipboard(self):
        try:
            clipboard = self.root.clipboard_get()
            words = [line.strip() for line in clipboard.split('\n') if line.strip()]
            
            added_count = 0
            for word in words[:500]:  # Limit paste
                if word not in self.words:
                    self.words.append(word)
                    self.repetitions[word] = 2
                    item_id = self.tree.insert('', tk.END, values=(word, 2))
                    self.word_to_item[word] = item_id
                    added_count += 1
            
            self.update_stats()
            messagebox.showinfo("Success", f"Imported {added_count} words from clipboard")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to read clipboard: {str(e)}")

    # ========== TEMPLATE MANAGEMENT ==========
    
    def load_templates(self):
        """Load saved templates"""
        template_file = "wordlist_templates.json"
        if os.path.exists(template_file):
            try:
                with open(template_file, 'r') as f:
                    self.templates = json.load(f)
            except:
                self.templates = {}
    
    def save_templates(self):
        """Save templates to file"""
        template_file = "wordlist_templates.json"
        try:
            with open(template_file, 'w') as f:
                json.dump(self.templates, f, indent=2)
        except Exception as e:
            messagebox.showerror("Error", f"Failed to save templates: {str(e)}")
    
    def save_template(self):
        name = tk.simpledialog.askstring("Save Template", "Enter template name:")
        if name:
            template = {
                'words': self.words,
                'repetitions': self.repetitions,
                'settings': self.get_current_settings(),
                'metadata': {
                    'created': datetime.now().isoformat(),
                    'version': '4.0'
                }
            }
            self.templates[name] = template
            self.save_templates()
            messagebox.showinfo("Success", f"Template '{name}' saved successfully")
    
    def load_template(self):
        if not self.templates:
            messagebox.showinfo("Info", "No templates saved yet")
            return
        
        # Create template selection dialog
        self.show_template_dialog()
    
    def show_template_dialog(self):
        dialog = tk.Toplevel(self.root)
        dialog.title("Load Template")
        dialog.geometry("400x300")
        dialog.transient(self.root)
        
        # Apply theme
        theme = self.themes[self.current_theme]
        dialog.configure(bg=theme['bg'])
        
        ttk.Label(dialog, text="Select Template:").pack(pady=10)
        
        listbox = tk.Listbox(dialog)
        for name in self.templates.keys():
            listbox.insert(tk.END, name)
        listbox.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        
        def load_selected():
            selection = listbox.curselection()
            if selection:
                name = listbox.get(selection[0])
                self.apply_template(name)
                dialog.destroy()
        
        ttk.Button(dialog, text="Load Selected", command=load_selected).pack(pady=10)
    
    def apply_template(self, name):
        if name in self.templates:
            template = self.templates[name]
            
            # Clear current data
            self.clear_all()
            
            # Apply template
            self.words = template['words'][:]
            self.repetitions = template['repetitions'].copy()
            
            # Update UI
            for word, rep in self.repetitions.items():
                item_id = self.tree.insert('', tk.END, values=(word, rep))
                self.word_to_item[word] = item_id
            
            # Apply settings
            settings = template['settings']
            self.apply_settings(settings)
            
            self.update_stats()
            messagebox.showinfo("Success", f"Template '{name}' loaded successfully")
    
    def manage_templates(self):
        # Simple template management dialog
        self.show_template_management()
    
    def show_template_management(self):
        dialog = tk.Toplevel(self.root)
        dialog.title("Manage Templates")
        dialog.geometry("500x400")
        dialog.transient(self.root)
        
        # Apply theme
        theme = self.themes[self.current_theme]
        dialog.configure(bg=theme['bg'])
        
        ttk.Label(dialog, text="Saved Templates:").pack(pady=10)
        
        listbox = tk.Listbox(dialog)
        for name in self.templates.keys():
            listbox.insert(tk.END, name)
        listbox.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        
        button_frame = ttk.Frame(dialog)
        button_frame.pack(pady=10)
        
        def delete_selected():
            selection = listbox.curselection()
            if selection:
                name = listbox.get(selection[0])
                if messagebox.askyesno("Confirm", f"Delete template '{name}'?"):
                    del self.templates[name]
                    self.save_templates()
                    listbox.delete(selection[0])
        
        ttk.Button(button_frame, text="Delete Selected", 
                  command=delete_selected).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="Close", 
                  command=dialog.destroy).pack(side=tk.LEFT, padx=5)

    # ========== PROJECT MANAGEMENT ==========
    
    def new_project(self):
        if self.words and not messagebox.askyesno("Confirm", "Current project will be lost. Continue?"):
            return
        
        self.clear_all()
        self.current_project = None
        self.status_label.config(text="New project created")
    
    def save_project(self):
        filename = filedialog.asksaveasfilename(
            title="Save Project",
            defaultextension=".wlproj",
            filetypes=[("Wordlist Project", "*.wlproj"), ("All files", "*.*")]
        )
        
        if filename:
            project = {
                'words': self.words,
                'repetitions': self.repetitions,
                'settings': self.get_current_settings(),
                'metadata': {
                    'created': datetime.now().isoformat(),
                    'version': '4.0'
                }
            }
            
            try:
                with open(filename, 'w') as f:
                    json.dump(project, f, indent=2)
                self.current_project = filename
                messagebox.showinfo("Success", f"Project saved to {filename}")
            except Exception as e:
                messagebox.showerror("Error", f"Failed to save project: {str(e)}")
    
    def load_project(self):
        filename = filedialog.askopenfilename(
            title="Load Project",
            filetypes=[("Wordlist Project", "*.wlproj"), ("All files", "*.*")]
        )
        
        if filename:
            try:
                with open(filename, 'r') as f:
                    project = json.load(f)
                
                # Clear current data
                self.clear_all()
                
                # Load project data
                self.words = project['words']
                self.repetitions = project['repetitions']
                
                # Update UI
                for word, rep in self.repetitions.items():
                    item_id = self.tree.insert('', tk.END, values=(word, rep))
                    self.word_to_item[word] = item_id
                
                # Apply settings
                self.apply_settings(project['settings'])
                
                self.current_project = filename
                self.update_stats()
                messagebox.showinfo("Success", f"Project loaded from {filename}")
                
            except Exception as e:
                messagebox.showerror("Error", f"Failed to load project: {str(e)}")
    
    def get_current_settings(self):
        return {
            'permutations': self.permutations_var.get(),
            'case_variations': self.case_var.get(),
            'leet_speak': self.leet_var.get(),
            'rules': {k: v.get() for k, v in self.rule_vars.items()},
            'character_sets': {k: v.get() for k, v in self.charset_vars.items()},
            'leet_level': self.leet_level_var.get(),
            'strength': {
                'min_length': self.min_length_var.get(),
                'max_length': self.max_length_var.get(),
                'require_upper': self.require_upper_var.get(),
                'require_lower': self.require_lower_var.get(),
                'require_digit': self.require_digit_var.get(),
                'require_special': self.require_special_var.get()
            }
        }
    
    def apply_settings(self, settings):
        self.permutations_var.set(settings.get('permutations', True))
        self.case_var.set(settings.get('case_variations', True))
        self.leet_var.set(settings.get('leet_speak', False))
        
        rule_settings = settings.get('rules', {})
        for key, value in rule_settings.items():
            if key in self.rule_vars:
                self.rule_vars[key].set(value)
        
        charset_settings = settings.get('character_sets', {})
        for key, value in charset_settings.items():
            if key in self.charset_vars:
                self.charset_vars[key].set(value)
        
        strength_settings = settings.get('strength', {})
        self.min_length_var.set(strength_settings.get('min_length', '1'))
        self.max_length_var.set(strength_settings.get('max_length', '100'))
        self.require_upper_var.set(strength_settings.get('require_upper', False))
        self.require_lower_var.set(strength_settings.get('require_lower', False))
        self.require_digit_var.set(strength_settings.get('require_digit', False))
        self.require_special_var.set(strength_settings.get('require_special', False))
        
        self.leet_level_var.set(settings.get('leet_level', 'basic'))

    # ========== BATCH PROCESSING ==========
    
    def batch_process(self):
        files = filedialog.askopenfilenames(
            title="Select Files for Batch Processing",
            filetypes=[("Text files", "*.txt"), ("CSV files", "*.csv"), ("All files", "*.*")]
        )
        
        if files:
            output_dir = filedialog.askdirectory(title="Select Output Directory")
            if output_dir:
                self.process_batch_files(files, output_dir)
    
    def process_batch_files(self, files, output_dir):
        def process():
            total_processed = 0
            for i, filename in enumerate(files):
                if self.stop_generation:
                    break
                
                self.status_label.config(text=f"Processing {os.path.basename(filename)}...")
                self.progress['value'] = (i / len(files)) * 100
                
                try:
                    # Import words from file
                    if filename.endswith('.csv'):
                        df = pd.read_csv(filename)
                        words = df.iloc[:, 0].dropna().astype(str).tolist()
                    else:
                        with open(filename, 'r', encoding='utf-8', errors='ignore') as f:
                            words = [line.strip() for line in f if line.strip()]
                    
                    # Generate wordlist
                    temp_words = words[:10]  # Use first 10 words for demo
                    combinations = set()
                    
                    # Simple combination generation
                    for r in range(1, min(4, len(temp_words) + 1)):
                        for combo in itertools.combinations(temp_words, r):
                            for perm in itertools.permutations(combo):
                                combinations.add(''.join(perm))
                    
                    # Save output
                    output_file = os.path.join(output_dir, f"batch_{os.path.basename(filename)}")
                    with open(output_file, 'w') as f:
                        for combo in combinations:
                            f.write(combo + '\n')
                    
                    total_processed += 1
                    
                except Exception as e:
                    print(f"Error processing {filename}: {str(e)}")
            
            self.root.after(0, lambda: messagebox.showinfo("Batch Complete", 
                                 f"Processed {total_processed}/{len(files)} files"))
            self.root.after(0, self.reset_progress)
        
        threading.Thread(target=process, daemon=True).start()
    
    def schedule_generation(self):
        """Schedule automated generation"""
        schedule_window = tk.Toplevel(self.root)
        schedule_window.title("Schedule Generation")
        schedule_window.geometry("400x300")
        schedule_window.transient(self.root)
        
        # Apply theme
        theme = self.themes[self.current_theme]
        schedule_window.configure(bg=theme['bg'])
        
        ttk.Label(schedule_window, text="Schedule Configuration", font=('Arial', 12, 'bold')).pack(pady=10)
        
        # Schedule options
        options_frame = ttk.Frame(schedule_window)
        options_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)
        
        ttk.Label(options_frame, text="Schedule Type:").grid(row=0, column=0, sticky=tk.W, padx=(0, 10))
        schedule_type = ttk.Combobox(options_frame, values=["Daily", "Weekly", "Monthly", "Custom"])
        schedule_type.set("Daily")
        schedule_type.grid(row=0, column=1, sticky=tk.W, padx=(0, 20))
        
        ttk.Label(options_frame, text="Time (HH:MM):").grid(row=0, column=2, sticky=tk.W, padx=(0, 10))
        time_entry = ttk.Entry(options_frame)
        time_entry.insert(0, "02:00")
        time_entry.grid(row=0, column=3, sticky=tk.W)
        
        ttk.Label(options_frame, text="Output Directory:").grid(row=1, column=0, sticky=tk.W, padx=(0, 10))
        output_dir_var = tk.StringVar()
        ttk.Entry(options_frame, textvariable=output_dir_var).grid(row=1, column=1, columnspan=3, sticky=tk.W+tk.E, pady=5)
        
        def browse_output():
            directory = filedialog.askdirectory()
            if directory:
                output_dir_var.set(directory)
        
        ttk.Button(options_frame, text="Browse", command=browse_output).grid(row=2, column=0, pady=5)
        
        def start_schedule():
            messagebox.showinfo("Scheduled", "Generation scheduled successfully!\n(Note: This is a demo feature)")
            schedule_window.destroy()
        
        ttk.Button(schedule_window, text="Start Schedule", command=start_schedule).pack(pady=10)

    # ========== ANALYTICS ==========
    
    def analyze_strength(self):
        if not self.words:
            messagebox.showwarning("Warning", "No words to analyze")
            return
        
        analysis = self.perform_strength_analysis()
        self.display_analysis(analysis)
    
    def perform_strength_analysis(self):
        analysis = {
            'total_words': len(self.words),
            'length_stats': {},
            'character_analysis': {},
            'common_patterns': [],
            'strength_distribution': {'very_weak': 0, 'weak': 0, 'medium': 0, 'strong': 0, 'very_strong': 0}
        }
        
        # Length analysis
        lengths = [len(word) for word in self.words]
        analysis['length_stats'] = {
            'min': min(lengths) if lengths else 0,
            'max': max(lengths) if lengths else 0,
            'average': sum(lengths) / len(lengths) if lengths else 0,
            'median': sorted(lengths)[len(lengths)//2] if lengths else 0
        }
        
        # Character analysis
        all_chars = ''.join(self.words)
        char_count = Counter(all_chars)
        analysis['character_analysis'] = dict(char_count.most_common(15))
        
        # Strength analysis
        for word in self.words:
            strength = self.assess_password_strength_advanced(word)
            analysis['strength_distribution'][strength] += 1
        
        # Common patterns
        analysis['common_patterns'] = self.detect_common_patterns()
        
        return analysis
    
    def assess_password_strength_advanced(self, password):
        """Advanced password strength assessment"""
        score = 0
        
        # Length score (0-3 points)
        if len(password) >= 16: score += 3
        elif len(password) >= 12: score += 2
        elif len(password) >= 8: score += 1
        
        # Character variety (0-4 points)
        if any(c.islower() for c in password): score += 1
        if any(c.isupper() for c in password): score += 1
        if any(c.isdigit() for c in password): score += 1
        if any(not c.isalnum() for c in password): score += 1
        
        # Entropy bonus
        unique_chars = len(set(password))
        if unique_chars / len(password) > 0.8: score += 1
        
        # Pattern penalty
        if self.has_common_pattern(password): score -= 1
        
        if score >= 6: return 'very_strong'
        elif score >= 4: return 'strong'
        elif score >= 3: return 'medium'
        elif score >= 1: return 'weak'
        else: return 'very_weak'
    
    def has_common_pattern(self, password):
        """Check for common weak patterns"""
        common_patterns = [
            '123', 'abc', 'qwerty', 'password', 'admin'
        ]
        password_lower = password.lower()
        return any(pattern in password_lower for pattern in common_patterns)
    
    def detect_common_patterns(self):
        """Detect common patterns in passwords"""
        patterns = []
        
        # Check for sequential numbers
        for word in self.words:
            if re.search(r'123|234|345|456|567|678|789', word):
                patterns.append(f"Sequential numbers in: {word}")
        
        # Check for repeated characters
        for word in self.words:
            if re.search(r'(.)\1{2,}', word):  # 3 or more repeated chars
                patterns.append(f"Repeated characters in: {word}")
        
        return patterns[:10]  # Return top 10 patterns
    
    def display_analysis(self, analysis):
        self.stats_text.delete('1.0', tk.END)
        
        report = [
            "=== ADVANCED PASSWORD STRENGTH ANALYSIS ===",
            f"Total Words Analyzed: {analysis['total_words']}",
            "",
            "📏 LENGTH STATISTICS:",
            f"  Minimum: {analysis['length_stats']['min']}",
            f"  Maximum: {analysis['length_stats']['max']}",
            f"  Average: {analysis['length_stats']['average']:.2f}",
            f"  Median: {analysis['length_stats']['median']}",
            "",
            "🛡️ STRENGTH DISTRIBUTION:",
            f"  Very Weak: {analysis['strength_distribution']['very_weak']}",
            f"  Weak: {analysis['strength_distribution']['weak']}",
            f"  Medium: {analysis['strength_distribution']['medium']}",
            f"  Strong: {analysis['strength_distribution']['strong']}",
            f"  Very Strong: {analysis['strength_distribution']['very_strong']}",
            "",
            "🔤 TOP 15 MOST COMMON CHARACTERS:",
        ]
        
        for char, count in analysis['character_analysis'].items():
            display_char = repr(char)[1:-1]  # Handle special characters
            report.append(f"  '{display_char}': {count}")
        
        if analysis['common_patterns']:
            report.extend(["", "🚨 COMMON WEAK PATTERNS DETECTED:"])
            report.extend([f"  {pattern}" for pattern in analysis['common_patterns']])
        
        self.stats_text.insert('1.0', '\n'.join(report))
    
    def compare_wordlists(self):
        """Compare multiple wordlists"""
        files = filedialog.askopenfilenames(
            title="Select Wordlists to Compare",
            filetypes=[("Text files", "*.txt"), ("All files", "*.*")]
        )
        
        if len(files) < 2:
            messagebox.showwarning("Warning", "Please select at least 2 wordlists to compare")
            return
        
        comparison_data = {}
        
        for file in files:
            try:
                with open(file, 'r', encoding='utf-8', errors='ignore') as f:
                    passwords = [line.strip() for line in f if line.strip()]
                
                filename = os.path.basename(file)
                comparison_data[filename] = {
                    'count': len(passwords),
                    'avg_length': sum(len(p) for p in passwords) / len(passwords) if passwords else 0,
                    'unique_chars': len(set(''.join(passwords))),
                    'strength_distribution': {'very_weak': 0, 'weak': 0, 'medium': 0, 'strong': 0, 'very_strong': 0}
                }
                
                # Analyze strength
                for pwd in passwords:
                    strength = self.assess_password_strength_advanced(pwd)
                    comparison_data[filename]['strength_distribution'][strength] += 1
                    
            except Exception as e:
                messagebox.showerror("Error", f"Failed to analyze {file}: {str(e)}")
                return
        
        # Display comparison
        self.display_comparison(comparison_data)
    
    def display_comparison(self, comparison_data):
        """Display wordlist comparison results"""
        comparison_window = tk.Toplevel(self.root)
        comparison_window.title("Wordlist Comparison Results")
        comparison_window.geometry("800x600")
        
        # Apply theme
        theme = self.themes[self.current_theme]
        comparison_window.configure(bg=theme['bg'])
        
        text_widget = scrolledtext.ScrolledText(comparison_window, wrap=tk.WORD)
        text_widget.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        report = ["=== WORDLIST COMPARISON RESULTS ===\n"]
        
        for filename, data in comparison_data.items():
            report.extend([
                f"📁 {filename}",
                f"  Total Passwords: {data['count']:,}",
                f"  Average Length: {data['avg_length']:.2f}",
                f"  Unique Characters: {data['unique_chars']}",
                "  Strength Distribution:",
                f"    Very Weak: {data['strength_distribution']['very_weak']}",
                f"    Weak: {data['strength_distribution']['weak']}",
                f"    Medium: {data['strength_distribution']['medium']}",
                f"    Strong: {data['strength_distribution']['strong']}",
                f"    Very Strong: {data['strength_distribution']['very_strong']}",
                ""
            ])
        
        text_widget.insert('1.0', '\n'.join(report))
        text_widget.config(state=tk.DISABLED)

    # ========== MARKOV CHAIN GENERATION ==========
    
    def generate_markov(self):
        """Generate passwords using Markov chains"""
        if not self.words:
            messagebox.showwarning("Warning", "Please add some words first")
            return
        
        try:
            order = int(self.markov_order.get())
            count = int(self.markov_count.get())
        except ValueError:
            messagebox.showwarning("Warning", "Please enter valid numbers")
            return
        
        # Advanced Markov chain implementation
        markov_passwords = self.advanced_markov_generation(order, count)
        
        # Add to current word list
        for pwd in markov_passwords:
            if pwd not in self.words:
                self.words.append(pwd)
                self.repetitions[pwd] = 1
                item_id = self.tree.insert('', tk.END, values=(pwd, 1))
                self.word_to_item[pwd] = item_id
        
        self.update_stats()
        messagebox.showinfo("Success", f"Generated {len(markov_passwords)} Markov passwords")
    
    def advanced_markov_generation(self, order, count):
        """Advanced Markov chain password generation"""
        # Training data is our current words
        training_data = ' '.join(self.words)
        
        if len(training_data) < order:
            return []
        
        # Build advanced Markov model
        model = defaultdict(Counter)
        for i in range(len(training_data) - order):
            key = training_data[i:i + order]
            next_char = training_data[i + order]
            model[key][next_char] += 1
        
        # Generate passwords
        passwords = set()
        attempts = 0
        max_attempts = count * 20
        
        while len(passwords) < count and attempts < max_attempts:
            attempts += 1
            
            # Start with random key that has followers
            valid_keys = [k for k in model.keys() if model[k]]
            if not valid_keys:
                break
                
            key = random.choice(valid_keys)
            password = key
            
            # Generate until we hit a stop or reach reasonable length
            while len(password) < 50:  # Increased max password length
                if key in model and model[key]:
                    # Weighted random choice based on frequency
                    choices, weights = zip(*model[key].items())
                    next_char = random.choices(choices, weights=weights)[0]
                    password += next_char
                    key = password[-order:]
                else:
                    break
            
            # Apply filters
            if (1 <= len(password) <= 100 and  # Increased length limits
                not self.has_common_pattern(password) and
                len(set(password)) >= 2):  # Reduced uniqueness requirement
                passwords.add(password)
        
        return list(passwords)[:count]

    # ========== MAIN GENERATION ==========
    
    def generate_wordlist(self):
        if not self.words:
            messagebox.showwarning("Warning", "Please add some words first")
            return
        
        # Calculate total positions
        total_positions = sum(self.repetitions.values())
        
        # Estimate size and warn if too large
        estimated = self.estimate_combinations()
        if estimated > 1000000:
            if not messagebox.askyesno("Warning", 
                                     f"Total positions: {total_positions}\n"
                                     f"This will generate approximately {estimated:,} combinations.\n"
                                     f"This may take a long time and use significant memory.\n"
                                     f"Continue?"):
                return
        
        filename = filedialog.asksaveasfilename(
            title="Save Wordlist",
            defaultextension="." + self.format_var.get(),
            filetypes=[
                ("Text files", "*.txt"),
                ("PDF files", "*.pdf"),
                ("Excel files", "*.xlsx"),
                ("JSON files", "*.json"),
                ("SQLite database", "*.db"),
                ("ZIP archive", "*.zip"),
                ("All files", "*.*")
            ]
        )
        
        if filename:
            self.stop_generation = False
            self.progress['value'] = 0
            self.status_label.config(text="Generating wordlist...")
            
            self.generation_thread = threading.Thread(
                target=self._generate_in_thread, 
                args=(filename,),
                daemon=True
            )
            self.generation_thread.start()
    
    def _generate_in_thread(self, filename):
        try:
            combinations = self.generate_combinations()
            
            if self.deduplicate_var.get():
                combinations = list(set(combinations))
            
            self.root.after(0, self._update_progress_mid, len(combinations))
            
            success = self.save_wordlist(combinations, filename)
            
            self.root.after(0, self._generation_complete, success, len(combinations), filename)
            
        except Exception as e:
            self.root.after(0, self._generation_error, str(e))
    
    def save_wordlist(self, combinations, filename):
        format_type = self.format_var.get()
        
        try:
            if format_type == "txt":
                with open(filename, 'w', encoding='utf-8') as f:
                    for combo in combinations:
                        f.write(combo + '\n')
            
            elif format_type == "pdf":
                self.save_as_pdf(combinations, filename)
            
            elif format_type == "xlsx":
                df = pd.DataFrame(combinations, columns=['Passwords'])
                df.to_excel(filename, index=False)
            
            elif format_type == "json":
                with open(filename, 'w') as f:
                    json.dump(combinations, f, indent=2)
            
            elif format_type == "db":
                self.save_as_sqlite(combinations, filename)
            
            elif format_type == "zip":
                self.save_as_zip(combinations, filename)
                
            return True
            
        except Exception as e:
            return False
    
    def save_as_pdf(self, combinations, filename):
        doc = SimpleDocTemplate(filename, pagesize=A4)
        elements = []
        
        styles = getSampleStyleSheet()
        title = Paragraph("Ultimate Wordlist Generator Report", styles['Title'])
        elements.append(title)
        
        elements.append(Paragraph(f"Generated on: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}", styles['Normal']))
        elements.append(Paragraph(f"Total passwords: {len(combinations):,}", styles['Normal']))
        elements.append(Spacer(1, 0.2*inch))
        
        # Show first 500 entries
        display_data = combinations[:500]
        data = [['No.', 'Password']]
        for i, combo in enumerate(display_data, 1):
            data.append([str(i), combo])
        
        if len(combinations) > 500:
            data.append(['...', f'... and {len(combinations) - 500} more entries ...'])
        
        table = Table(data)
        table.setStyle(TableStyle([
            ('BACKGROUND', (0, 0), (-1, 0), colors.HexColor('#2b2b2b')),
            ('TEXTCOLOR', (0, 0), (-1, 0), colors.whitesmoke),
            ('ALIGN', (0, 0), (-1, -1), 'CENTER'),
            ('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold'),
            ('FONTSIZE', (0, 0), (-1, 0), 12),
            ('BOTTOMPADDING', (0, 0), (-1, 0), 12),
            ('BACKGROUND', (0, 1), (-1, -1), colors.beige),
            ('GRID', (0, 0), (-1, -1), 1, colors.black)
        ]))
        
        elements.append(table)
        doc.build(elements)
    
    def save_as_sqlite(self, combinations, filename):
        conn = sqlite3.connect(filename)
        cursor = conn.cursor()
        
        cursor.execute('''
            CREATE TABLE passwords (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                password TEXT UNIQUE,
                length INTEGER,
                strength TEXT,
                entropy REAL
            )
        ''')
        
        for password in combinations:
            strength = self.assess_password_strength_advanced(password)
            entropy = self.calculate_entropy(password)
            cursor.execute(
                "INSERT OR IGNORE INTO passwords (password, length, strength, entropy) VALUES (?, ?, ?, ?)",
                (password, len(password), strength, entropy)
            )
        
        conn.commit()
        conn.close()
    
    def calculate_entropy(self, password):
        """Calculate password entropy"""
        if not password:
            return 0
        
        char_set_size = len(set(password))
        return len(password) * math.log2(char_set_size) if char_set_size > 0 else 0
    
    def save_as_zip(self, combinations, filename):
        with zipfile.ZipFile(filename, 'w', zipfile.ZIP_DEFLATED) as zipf:
            # Save as text file inside zip
            txt_filename = os.path.splitext(os.path.basename(filename))[0] + '.txt'
            with zipf.open(txt_filename, 'w') as f:
                for combo in combinations:
                    f.write((combo + '\n').encode('utf-8'))
    
    def _update_progress_mid(self, count):
        self.status_label.config(text=f"Generated {count:,} combinations, saving...")
        self.progress['value'] = 50
    
    def _generation_complete(self, success, count, filename):
        self.progress['value'] = 100
        if success:
            self.status_label.config(text=f"Successfully generated {count:,} passwords")
            messagebox.showinfo("Success", 
                              f"Wordlist generated successfully!\n"
                              f"Total passwords: {count:,}\n"
                              f"Saved to: {filename}")
        else:
            self.status_label.config(text="Generation failed")
            messagebox.showerror("Error", "Failed to save wordlist")
        
        self.reset_progress()
    
    def _generation_error(self, error_msg):
        self.reset_progress()
        self.status_label.config(text="Generation failed")
        messagebox.showerror("Error", f"Failed to generate wordlist: {error_msg}")
    
    def reset_progress(self):
        self.progress['value'] = 0
        self.stop_generation = False

def main():
    root = tk.Tk()
    
    # Set window icon and title
    root.title("Ultimate Wordlist Generator v4.0")
    
    # Create and run application
    app = UltimateWordlistGenerator(root)
    root.mainloop()

if __name__ == "__main__":
    main()